"""Direct HOL subprocess management with clean interrupt support."""

import asyncio
import os
import signal
from pathlib import Path
from typing import Optional

HOLDIR = Path(os.environ.get("HOLDIR", Path.home() / "HOL"))
ETQ_PATH = Path(__file__).parent / "skills" / "hol" / "scripts" / "etq.sml"


class HOLSession:
    """Direct HOL subprocess management with clean interrupt support."""

    def __init__(self, workdir: str):
        self.workdir = Path(workdir)
        self.process: Optional[asyncio.subprocess.Process] = None
        self._buffer = b""

    async def start(self) -> str:
        """Start HOL subprocess."""
        if self.process and self.process.returncode is None:
            return "HOL already running"

        self.process = await asyncio.create_subprocess_exec(
            str(HOLDIR / "bin" / "hol"), "--zero",
            stdin=asyncio.subprocess.PIPE,
            stdout=asyncio.subprocess.PIPE,
            # Merge stderr to stdout: HOL's interactive mode sends all output
            # (warnings, errors, proof state) to stdout. Stderr is empty in
            # practice - only batch tools use it. Merging preserves ordering
            # with null-byte framing.
            stderr=asyncio.subprocess.STDOUT,
            cwd=self.workdir,
            start_new_session=True,  # New process group for clean kill
        )

        # Wait for initial prompt (null-terminated)
        output = await self._read_until_null(timeout=60)

        # Load etq.sml (goaltree mode helpers)
        if ETQ_PATH.exists():
            await self.send(ETQ_PATH.read_text(), timeout=30)

        # Load .hol_init.sml if present
        init_file = self.workdir / ".hol_init.sml"
        if init_file.exists():
            await self.send(init_file.read_text(), timeout=60)

        return f"HOL started (PID {self.process.pid})"

    async def send(self, sml_code: str, timeout: float = 5) -> str:
        """Send SML code and wait for response."""
        if not self.process or self.process.returncode is not None:
            return "ERROR: HOL not running"

        # Send code with null terminator
        self.process.stdin.write(sml_code.encode() + b'\0')
        await self.process.stdin.drain()

        try:
            return await self._read_until_null(timeout=timeout)
        except asyncio.TimeoutError:
            self.interrupt()
            try:
                remaining = await self._read_until_null(timeout=5)
            except asyncio.TimeoutError:
                remaining = ""
            # HOL outputs extra null byte after interrupt - drain it
            self._buffer = self._buffer.lstrip(b'\0')
            await self._drain_null()
            msg = f"TIMEOUT after {timeout}s - sent interrupt."
            return f"{msg}\n{remaining}" if remaining else msg

    async def _drain_null(self):
        """Drain extra null byte from pipe after interrupt."""
        try:
            b = await asyncio.wait_for(self.process.stdout.read(1), timeout=0.1)
            if b and b != b'\0':
                self._buffer = b + self._buffer
        except asyncio.TimeoutError:
            pass

    async def _read_until_null(self, timeout: float) -> str:
        """Read stdout until null byte."""
        async def read_loop():
            while True:
                # Check buffer first - may already have complete response
                if b'\0' in self._buffer:
                    before, self._buffer = self._buffer.split(b'\0', 1)
                    return before.decode()

                chunk = await self.process.stdout.read(4096)
                if not chunk:
                    raise RuntimeError("HOL process died unexpectedly")
                self._buffer += chunk

        return await asyncio.wait_for(read_loop(), timeout=timeout)

    def interrupt(self):
        """Send SIGINT to entire process group."""
        if self.process and self.process.returncode is None:
            try:
                pgid = os.getpgid(self.process.pid)
                os.killpg(pgid, signal.SIGINT)
            except (ProcessLookupError, PermissionError):
                pass

    async def stop(self):
        """Kill the HOL process group and wait for cleanup."""
        if self.process and self.process.returncode is None:
            try:
                pgid = os.getpgid(self.process.pid)
                os.killpg(pgid, signal.SIGTERM)
            except (ProcessLookupError, PermissionError):
                pass
            # Wait for process to actually terminate
            try:
                await asyncio.wait_for(self.process.wait(), timeout=5)
            except asyncio.TimeoutError:
                # Force kill if it doesn't terminate
                try:
                    self.process.kill()
                    await self.process.wait()
                except Exception:
                    pass
        self.process = None
        self._buffer = b""

    @property
    def is_running(self) -> bool:
        return self.process is not None and self.process.returncode is None

    async def __aenter__(self):
        await self.start()
        return self

    async def __aexit__(self, exc_type, exc_val, exc_tb):
        await self.stop()
