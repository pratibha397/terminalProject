# Terminator

A custom terminal emulator and shell written in C for Linux (X11).

## Prerequisites

- Linux with X11
- GCC
- X11 development libraries (`libx11-dev` on Debian/Ubuntu)

```bash
sudo apt install build-essential libx11-dev
```

## Build

```bash
gcc -O2 -Wall -o terminator terminal.c -lX11 -lpthread
```

## Run

```bash
./terminator                  # thread mode (default)
./terminator useProcess=True  # process mode
```

## Features

- Multiple tabs (up to 8)
- Shared persistent command history (`~/.terminator_history`)
- Pipelines, redirections (`<`, `>`), background jobs (`&`)
- Job control: `jobs`, `fg`, `bg`, Ctrl+C, Ctrl+Z
- Variable expansion (`$VAR`, `$?`, `~`)
- Command substitution (`$(...)`, backticks)
- Multiline input (unclosed quotes, trailing `\`, trailing `|`)
- Tab completion (files in current directory)
- History search (Ctrl+R)
- Built-in script interpreter (`source`, `bash script.sh`, `*.sh`)
- `multiWatch ["cmd1", "cmd2", ...]` — run commands in parallel, restart every 2s
- Interactive programs (`vim`, `nano`, `less`, `top`, …) use the real TTY
- Rebindable keys via `~/.terminatorrc`

## Key Bindings

| Key              | Action              |
|------------------|---------------------|
| Left / Right     | Move cursor         |
| Up / Down        | History             |
| Ctrl+A           | Beginning of line   |
| Ctrl+E           | End of line         |
| Ctrl+U           | Delete to start     |
| Ctrl+K           | Delete to end       |
| Ctrl+W           | Delete previous word|
| Ctrl+L           | Clear screen        |
| Ctrl+D           | Delete char / close tab if empty |
| Ctrl+Shift+C     | Copy                |
| Ctrl+Shift+V     | Paste               |
| Ctrl+R           | History search      |
| Ctrl+T           | New tab             |
| Ctrl+S           | Next tab            |
| Ctrl+Shift+W     | Close tab           |
| Tab / Ctrl+Space | Filename completion |
| Ctrl+C           | Interrupt           |
| Ctrl+Z           | Suspend             |

Mouse: click tab labels or `[+]` to switch/create tabs. Scroll wheel to scroll output.

## Config (`~/.terminatorrc`)

One binding per line:

```
bind <modifiers>+<key> <action>
```

Example:

```
bind ctrl+x clear-screen
bind alt+t new-tab
```

Modifiers: `ctrl`, `shift`, `alt`  
Actions: `move-left`, `move-right`, `move-home`, `move-end`, `history-prev`, `history-next`, `delete-to-start`, `delete-to-end`, `delete-prev-word`, `clear-screen`, `eof`, `copy`, `paste`, `history-search`, `new-tab`, `close-tab`, `next-tab`, `complete`, `interrupt`, `suspend`

## Built-ins

`cd`, `exit`, `history`, `jobs`, `fg`, `bg`, `source` / `.`, `multiWatch`

Scripts support: comments, variables, `$1`–`$9`, `$#`, `$?`, `if` / `elif` / `else` / `fi` with `[ ... ]` tests, `exit [n]`.
