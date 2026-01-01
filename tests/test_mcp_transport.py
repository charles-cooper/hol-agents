"""Test MCP server via actual stdio transport (like Claude Code uses)."""

import asyncio
import json
import pytest
from pathlib import Path

FIXTURES_DIR = Path(__file__).parent / "fixtures"


async def run_mcp_request(proc, method: str, params: dict) -> dict:
    """Send JSON-RPC request to MCP server and get response."""
    request_id = id(params)  # unique id
    request = {
        "jsonrpc": "2.0",
        "id": request_id,
        "method": method,
        "params": params,
    }
    request_bytes = json.dumps(request).encode() + b"\n"
    proc.stdin.write(request_bytes)
    await proc.stdin.drain()

    # Read response line
    response_line = await asyncio.wait_for(proc.stdout.readline(), timeout=60)
    response = json.loads(response_line.decode())
    return response


async def test_mcp_stdio_empty_string():
    """Test that empty string responses work correctly via stdio transport."""
    proc = await asyncio.create_subprocess_exec(
        "python", "hol_mcp_server.py",
        stdin=asyncio.subprocess.PIPE,
        stdout=asyncio.subprocess.PIPE,
        stderr=asyncio.subprocess.PIPE,
        cwd=Path(__file__).parent.parent,
    )

    try:
        # Initialize
        resp = await run_mcp_request(proc, "initialize", {
            "protocolVersion": "2024-11-05",
            "capabilities": {},
            "clientInfo": {"name": "test", "version": "1.0"},
        })
        assert "result" in resp, f"init failed: {resp}"

        # Start session
        resp = await run_mcp_request(proc, "tools/call", {
            "name": "hol_start",
            "arguments": {"workdir": str(FIXTURES_DIR), "name": "stdio_test"},
        })
        assert "result" in resp, f"hol_start failed: {resp}"
        content = resp["result"]["content"][0]["text"]
        assert "HOL started" in content, f"Unexpected start result: {content}"

        # Send open command (shows bindings with file-based execution)
        resp = await run_mcp_request(proc, "tools/call", {
            "name": "hol_send",
            "arguments": {"session": "stdio_test", "command": "open boolTheory;", "timeout": 10},
        })
        assert "result" in resp, f"hol_send failed: {resp}"
        content = resp["result"]["content"][0]["text"]
        # With file-based execution, open shows bindings
        assert "thm" in content, f"Expected theorem bindings, got: {repr(content)[:100]}"

        # Send command with output after empty
        resp = await run_mcp_request(proc, "tools/call", {
            "name": "hol_send",
            "arguments": {"session": "stdio_test", "command": "1 + 1;", "timeout": 10},
        })
        assert "result" in resp, f"hol_send failed: {resp}"
        content = resp["result"]["content"][0]["text"]
        assert "2" in content, f"Expected 2, got: {repr(content)}"

        # Stop session
        resp = await run_mcp_request(proc, "tools/call", {
            "name": "hol_stop",
            "arguments": {"session": "stdio_test"},
        })

    finally:
        proc.terminate()
        await proc.wait()


async def test_mcp_stdio_stress():
    """Stress test via stdio transport."""
    proc = await asyncio.create_subprocess_exec(
        "python", "hol_mcp_server.py",
        stdin=asyncio.subprocess.PIPE,
        stdout=asyncio.subprocess.PIPE,
        stderr=asyncio.subprocess.PIPE,
        cwd=Path(__file__).parent.parent,
    )

    try:
        # Initialize
        await run_mcp_request(proc, "initialize", {
            "protocolVersion": "2024-11-05",
            "capabilities": {},
            "clientInfo": {"name": "test", "version": "1.0"},
        })

        # Start session
        await run_mcp_request(proc, "tools/call", {
            "name": "hol_start",
            "arguments": {"workdir": str(FIXTURES_DIR), "name": "stress_test"},
        })

        # Stress: many commands
        failures = []
        for i in range(50):
            resp = await run_mcp_request(proc, "tools/call", {
                "name": "hol_send",
                "arguments": {"session": "stress_test", "command": f"{i};", "timeout": 10},
            })
            content = resp.get("result", {}).get("content", [{}])[0].get("text", "")
            if str(i) not in content:
                failures.append(f"i={i}: expected {i} in {repr(content)}")

        assert not failures, f"stdio stress failures:\n" + "\n".join(failures[:10])

        # Stop
        await run_mcp_request(proc, "tools/call", {
            "name": "hol_stop",
            "arguments": {"session": "stress_test"},
        })

    finally:
        proc.terminate()
        await proc.wait()
