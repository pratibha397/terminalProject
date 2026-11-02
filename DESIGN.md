# Design

## Overview

Terminator is a single-process (or multi-process) X11 terminal emulator that embeds its own shell. The GUI and shell backends communicate over framed pipes.

## Architecture

### Two modes

- **Thread mode** (default): one pthread per tab. Lightweight; all tabs share the process address space. Tab state is thread-local.
- **Process mode** (`useProcess=True`): one forked process per tab. A crashed tab cannot take the others down. Each tab has private job tables and signal handling.

Both modes use the same framed protocol between GUI and backend:

```
[1 byte type][4 byte length][payload]
```

Types: `O` (output), `C` (cwd update), `L` (command line), `I` (interrupt), `Z` (suspend), `X` (command finished).

### GUI side

- X11 window, fixed-width font, tab bar, scrollable output buffer
- Main loop: `select()` on X11 fd, SIGCHLD self-pipe, and all tab output pipes
- Handles key events, mouse, selection/clipboard, window resize
- Never blocks waiting for a command; input can be typed in other tabs while one tab is busy

### Backend side (per tab)

- Owns its own job table, foreground process group, and pending command queue
- Runs the tokenizer, expander, builtins, and pipeline executor
- Captures stdout/stderr of non-interactive commands via pipes and streams them back as `O` frames
- Interactive programs (`vim`, `nano`, `less`, `top`, …) are given the real controlling TTY instead of a capture pipe

## Shell features implemented

| Feature | Implementation |
|---------|----------------|
| Pipelines / redirections | Custom tokenizer + `fork`/`pipe`/`dup2`/`execvp` |
| Job control | Process groups, `waitpid(WUNTRACED)`, `tcsetpgrp` for interactive programs |
| History | Shared memory (`mmap` + process-shared semaphore), persisted to disk |
| Variable / cmdsubst expansion | Recursive `$(...)` and backtick handling; `$VAR`, `$?`, `~` |
| Multiline | Quote / paren / backslash tracking; continuation prompt |
| Completion | Directory scan of tab CWD; longest common prefix or numbered list |
| Scripts | Own interpreter: `if`/`elif`/`else`/`fi`, `[ ]` tests, variables, positional params |
| multiWatch | Supervisor processes that re-run commands every 2 s; parent multiplexes their output |

## Key design choices

- **No external shell**: the program is both emulator and shell. Scripts are interpreted, never handed to `/bin/bash` (except for command substitution).
- **SIGCHLD self-pipe**: wakes `select()` without busy-waiting; each backend has its own pipe so wakeups are not stolen.
- **Foreground busy flag**: while a command runs in a tab, that tab rejects input editing but still accepts Ctrl+C/Z, tab switches, and history search. Lines typed in other tabs are queued.
- **Rebindable keys**: defaults are installed first; `~/.terminatorrc` can override them with conflict detection.
- **Interactive program hand-off**: full-screen programs receive `/dev/tty` and become the foreground process group of the terminal that launched Terminator; a note is printed in the tab so the user knows where to look.
