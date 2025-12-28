"""Tests for HOL session subprocess wrapper."""

import pytest
from pathlib import Path

from hol_session import HOLSession

FIXTURES_DIR = Path(__file__).parent / "fixtures"


async def test_hol_session():
    """Test HOL session basic functionality."""
    session = HOLSession(str(FIXTURES_DIR))
    try:
        result = await session.start()
        assert "HOL started" in result

        result = await session.send('1 + 1;', timeout=10)
        assert "2" in result

        assert session.is_running
    finally:
        await session.stop()
        assert not session.is_running


async def test_hol_session_context_manager():
    """Test HOL session as async context manager."""
    async with HOLSession(str(FIXTURES_DIR)) as session:
        assert session.is_running
        result = await session.send('3 + 4;', timeout=10)
        assert "7" in result
        assert session.is_running
    assert not session.is_running


async def test_hol_session_interrupt():
    """Test interrupting a long-running HOL command."""
    async with HOLSession(str(FIXTURES_DIR)) as session:
        # Start a long-running computation via short timeout
        result = await session.send('fun loop () = loop (); loop ();', timeout=1)
        assert "TIMEOUT" in result or "interrupt" in result.lower()

        # Session should still be usable after interrupt
        assert session.is_running
        result = await session.send('1 + 1;', timeout=10)
        assert "2" in result


async def test_hol_session_send_not_running():
    """Test sending to a stopped session returns error."""
    session = HOLSession(str(FIXTURES_DIR))
    result = await session.send('1 + 1;', timeout=10)
    assert "ERROR" in result


async def test_hol_session_start_already_running():
    async with HOLSession(str(FIXTURES_DIR)) as session:
        pid = session.process.pid
        result = await session.start()
        assert "already running" in result.lower()
        assert session.process.pid == pid


async def test_hol_session_sequential_sends():
    """Test sequential sends return correct outputs in order."""
    async with HOLSession(str(FIXTURES_DIR)) as session:
        for i in range(10):
            result = await session.send(f'{i};', timeout=10)
            assert str(i) in result, f"Expected {i} in result, got: {result}"


async def test_hol_session_post_interrupt_sync():
    """Test that session resyncs correctly after interrupt.

    After timeout/interrupt, buffer and pipe may have stale data.
    Verify subsequent commands work correctly.
    """
    async with HOLSession(str(FIXTURES_DIR)) as session:
        # Trigger interrupt with a timeout
        result = await session.send('fun loop () = loop (); loop ();', timeout=1)
        assert "TIMEOUT" in result or "interrupt" in result.lower()

        # Session should resync - send a few commands and verify correct outputs
        for i in range(5):
            result = await session.send(f'{100 + i};', timeout=10)
            assert str(100 + i) in result, f"Expected {100+i} after interrupt, got: {result}"
