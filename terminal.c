// terminator - a custom terminal emulator + shell in c for linux (x11)

// cs69201 term project

// build: gcc -o2 -wall -o terminator terminalnew.c -lx11

#define _GNU_SOURCE
#include <X11/Xlib.h>
#include <X11/Xatom.h>
#include <X11/Xutil.h>
#include <X11/keysym.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <sys/wait.h>
#include <sys/select.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <errno.h>
#include <ctype.h>
#include <pwd.h>
#include <limits.h>
#include <signal.h>
#include <time.h>
#include <dirent.h>
#include <stdint.h>
#include <stdarg.h>
#include <semaphore.h>
#include <glob.h>
#include <pthread.h>

#define MAX_TABS          8
#define MAX_LINES         2000
#define MAX_LINE_LEN      1024
#define MAX_INPUT_LEN     4096
#define MAX_HISTORY       10000
#define MAX_JOBS          64
#define MAX_PIPELINE      16
#define MAX_MATCHES       96
#define FONT_NAME         "fixed"
#define CHAR_W            8
#define CHAR_H            14
#define TAB_BAR_H         22
#define PROMPT_MAX        256
#define MW_DASHES         "----------------------------------------------------"
#define FRAME_HDR         5          // 1 byte type + 4 byte length

// types

typedef struct {
    char  lines[MAX_LINES][MAX_LINE_LEN];
    int   nlines;
    int   scroll;
    char  input[MAX_INPUT_LEN];
    int   input_len;
    int   cursor;
    char  cwd[PATH_MAX];
    int   last_status;
    int   multiline;
    char  pending[MAX_INPUT_LEN];
    char  pend_sep[2];        // separator to place before the next chunk
    int   hist_idx;
    int   searching;
    char  search_term[256];
    int   partial;            // last buffer line has no newline yet
    int   completing;         // waiting for a digit pick after tab list
    int   fg_busy;            // this tab's fg command is running or queued (thread mode): input line accepts nothing until it ends
    int   cmatch_n;
    int   cword_start;
    char  cmatch[MAX_MATCHES][256];
    int   out_fd;             // tab-child side: framed output to the gui
    int   net_len;            // gui side: frame reassembly buffer
    char  net_buf[16384];
} Tab;

typedef struct {
    pid_t pgid;               // process group leader
    char  cmd[256];
    int   status;             // 0 = running, 1 = stopped
    int   job_id;
    int   cap_fd;             // output capture pipe, -1 if none
} Job;

typedef struct {
    Display *dpy;
    Window   win;
    GC       gc;
    int      screen;
    int      width, height;
    Atom     wm_delete;
    XFontStruct *font;

    Tab      tabs[MAX_TABS];
    int      ntabs;
    int      active;

    // the job table, the fg-job markers and the multiwatch flag are not
    // here: they are thread-local globals, one private set per tab backend

    int      process_mode;    // 0 = thread mode, 1 = process mode
} Term;

// shared history: mapped map_shared before any fork so every process sees one copy; guarded by a process-shared semaphore

typedef struct {
    sem_t lock;
    int   count;
    char  cmds[MAX_HISTORY][MAX_INPUT_LEN];
} SharedHist;

typedef struct {
    int    mods;
    KeySym ks;
    int    action;
    int    custom;            // set once overridden from ~/.terminatorrc
} Binding;

#define MOD_CTRL  1
#define MOD_SHIFT 2
#define MOD_ALT   4

enum {
    A_NONE = 0,
    A_LEFT, A_RIGHT, A_HOME, A_END,
    A_HISTUP, A_HISTDN,
    A_DELSTART, A_DELEND, A_DELWORD,
    A_CLEAR, A_EOFDEL, A_COPY, A_PASTE,
    A_SEARCH, A_NEWTAB, A_CLOSETAB, A_NEXTTAB,
    A_COMPLETE, A_INTR, A_SUSP
};

// globals

static Term term;
static SharedHist *sh = NULL;

// thread-local backend state: a tab backend is one pthread (thread mode)
// or one process (process mode); each owns a private copy of these, so two
// tabs never share a tokenizer, a job table or a foreground job
static __thread int sigchld_rfd = -1, sigchld_wfd = -1;
static __thread int am_tab_child = 0; // this backend never touches x11
static __thread int am_tab_thread = 0;// backend is a pthread, not a fork
static __thread int my_in_fd = -1;    // backend: gui -> tab command pipe
static __thread int my_out_fd = -1;   // backend: tab -> gui output pipe

static __thread Job  tl_jobs[MAX_JOBS];      // per-backend job table
static __thread int  tl_njobs = 0;
static __thread int  tl_next_job_id = 1;
static __thread pid_t tl_fg_pgid = 0;        // this backend's fg job
static __thread int  tl_fg_running = 0;

static int mw_active = 0;             // gui-side multiwatch flag (inline mode)

static pid_t tab_pid[MAX_TABS];
static int   tab_out_fd[MAX_TABS];    // gui side: tab -> gui output pipe
static int   tab_in_fd[MAX_TABS];     // gui side: gui -> tab command pipe

static char clip[65536];              // our copy of the copied text
static int  paste_pending = 0;
static Atom sel_prop_atom = None;
static Atom clip_atom = None;

static Binding bindings[64];
static int   nbindings = 0;
static char  rc_warn[4096];

static __thread char child_pend[8][MAX_INPUT_LEN]; // typed while a fg job
static __thread int  child_npend = 0;              // runs in this tab (queued)

// inline fallback mode (used only if a tab backend could not be started):
// lines typed in a tab while a foreground job ran are queued here by
// wait_group() and run once that job finishes
static int  gui_pend_tab[8];
static char gui_pend_cmd[8][MAX_INPUT_LEN];
static int  gui_npend = 0;

// forward declarations

static void redraw(void);
static void tab_append(Tab *t, const char *text);
static void run_command(Tab *t, char *cmdline);
static void execute_line(Tab *t, char *cmdline);
static int  run_pipeline(Tab *t, char *cmdline, int background);
static void run_multiWatch(Tab *t, char *cmdline);
static void run_script(Tab *t, const char *filename, char **args, int argc);
static void do_tab_completion(Tab *t);
static void close_current_tab(void);
static void new_tab(void);
static int  wait_group(Tab *t, pid_t pgid, pid_t leader, int cap_fd_in,
                       int *stopped_out);
static void expand_cmdsubst(char *line, size_t sz);
static void expand_variables(char *line, size_t sz, int last_status);
static int  tokenize_pipeline(char *line, char *cmds[][64], int *cmd_argc,
                              int max_cmds, char **redir_in, char **redir_out);
static void tab_child_main(Tab *t, int in_fd, int out_fd);
static void do_hist_search(Tab *t);
static void input_insert(Tab *t, const char *s, int n);
static void run_queued_gui_commands(void);
static int  is_interactive_cmd(const char *cmd);
static int  cmd_is_interactive(const char *line);

// small utilities

static void die(const char *msg) {
    perror(msg);
    exit(1);
}

static char *get_home(void) {
    struct passwd *pw = getpwuid(getuid());
    return pw ? pw->pw_dir : getenv("HOME");
}

static void safe_copy(char *dst, size_t dstsz, const char *src) {
    if (dstsz == 0) return;
    size_t len = strnlen(src, dstsz - 1);
    memcpy(dst, src, len);
    dst[len] = '\0';
}

// framed pipe messages (gui <-> tab in process mode): 1 type byte +
// 4-byte length + payload; o=output, c=cwd, l=line, i=interrupt,
// z=suspend, x=done

static void send_frame(int fd, char type, const char *data, size_t len) {
    if (fd < 0) return;
    size_t total = FRAME_HDR + len;
    char *buf = malloc(total);
    if (!buf) return;
    uint32_t l = (uint32_t)len;
    buf[0] = type;
    memcpy(buf + 1, &l, 4);
    if (len) memcpy(buf + FRAME_HDR, data, len);
    size_t off = 0;
    while (off < total) {
        ssize_t n = write(fd, buf + off, total - off);
        if (n <= 0) {
            if (n < 0 && errno == EINTR) continue;
            break;
        }
        off += (size_t)n;
    }
    free(buf);
}

// reads exactly one frame. returns 1 on success, <=0 on eof/error.
// frames bigger than cap-1 are drained and reported empty.
static int read_frame(int fd, char *type, char *payload, size_t cap,
                      size_t *plen) {
    char hdr[FRAME_HDR];
    size_t got = 0;
    while (got < FRAME_HDR) {
        ssize_t n = read(fd, hdr + got, FRAME_HDR - got);
        if (n <= 0) {
            if (n < 0 && errno == EINTR) continue;
            return -1;
        }
        got += (size_t)n;
    }
    *type = hdr[0];
    uint32_t len;
    memcpy(&len, hdr + 1, 4);
    if (len >= cap) {                     // too big: drain and discard
        size_t left = len;
        char sink[4096];
        while (left) {
            ssize_t n = read(fd, sink, left < sizeof(sink) ? left : sizeof(sink));
            if (n <= 0) break;
            left -= (size_t)n;
        }
        payload[0] = '\0';
        *plen = 0;
        return 1;
    }
    got = 0;
    while (got < len) {
        ssize_t n = read(fd, payload + got, len - got);
        if (n <= 0) {
            if (n < 0 && errno == EINTR) continue;
            return -1;
        }
        got += (size_t)n;
    }
    payload[len] = '\0';
    *plen = len;
    return 1;
}

// tab text buffer

// in a tab child every append is shipped to the gui as an 'o' frame, in
// the gui process it lands in the tab's own buffer; 'partial' keeps a
// chunk without a newline attached to its line so streamed pipe output
// is not split mid-line
static void tab_append(Tab *t, const char *text) {
    if (am_tab_child) {
        if (my_out_fd >= 0) send_frame(my_out_fd, 'O', text, strlen(text));
        return;
    }
    const char *p = text;
    while (*p) {
        if (t->partial && t->nlines > 0) {
            int l = (int)strlen(t->lines[t->nlines - 1]);
            while (*p && *p != '\n' && l < MAX_LINE_LEN - 1)
                t->lines[t->nlines - 1][l++] = *p++;
            t->lines[t->nlines - 1][l] = '\0';
            if (*p == '\n') { p++; t->partial = 0; continue; }
            if (*p == '\0') return;
            t->partial = 0;                 // line full: start a new one
            continue;
        }
        if (t->nlines >= MAX_LINES - 1) {
            memmove(t->lines[0], t->lines[1], (MAX_LINES - 1) * MAX_LINE_LEN);
            t->nlines--;
            t->partial = 0;
        }
        int len = 0;
        while (p[len] && p[len] != '\n' && len < MAX_LINE_LEN - 1) len++;
        memcpy(t->lines[t->nlines], p, len);
        t->lines[t->nlines][len] = '\0';
        t->nlines++;
        p += len;
        if (*p == '\n') { p++; t->partial = 0; }
        else if (*p == '\0') t->partial = 1;
        else t->partial = 0;
    }
}

// shared history

static void history_init(void) {
    sh = mmap(NULL, sizeof(SharedHist), PROT_READ | PROT_WRITE,
              MAP_SHARED | MAP_ANONYMOUS | MAP_NORESERVE, -1, 0);
    if (sh == MAP_FAILED) die("terminator: mmap history");
    memset(sh, 0, sizeof(SharedHist));
    if (sem_init(&sh->lock, 1, 1) != 0) die("terminator: sem_init");
    sh->count = 0;
}

// caller must hold sh->lock

static void save_history_locked(void) {
    char path[PATH_MAX];
    snprintf(path, sizeof(path), "%s/.terminator_history", get_home());
    FILE *f = fopen(path, "w");
    if (!f) return;
    for (int i = 0; i < sh->count; i++)
        fprintf(f, "%s\n", sh->cmds[i]);
    fclose(f);
}

static void save_history(void) {
    if (!sh) return;
    sem_wait(&sh->lock);
    save_history_locked();
    sem_post(&sh->lock);
}

static void load_history(void) {
    char path[PATH_MAX];
    snprintf(path, sizeof(path), "%s/.terminator_history", get_home());
    FILE *f = fopen(path, "r");
    if (!f) return;
    char line[MAX_INPUT_LEN];
    sem_wait(&sh->lock);
    while (fgets(line, sizeof(line), f) && sh->count < MAX_HISTORY) {
        size_t len = strlen(line);
        if (len && line[len - 1] == '\n') line[--len] = 0;
        if (len) {
            safe_copy(sh->cmds[sh->count], MAX_INPUT_LEN, line);
            sh->count++;
        }
    }
    sem_post(&sh->lock);
    fclose(f);
}

static void add_to_history(const char *cmd) {
    if (!cmd || !*cmd) return;
    sem_wait(&sh->lock);
    if (sh->count > 0 && strcmp(sh->cmds[sh->count - 1], cmd) == 0) {
        sem_post(&sh->lock);
        return;
    }
    if (sh->count < MAX_HISTORY) {
        safe_copy(sh->cmds[sh->count], MAX_INPUT_LEN, cmd);
        sh->count++;
    } else {
        memmove(sh->cmds[0], sh->cmds[1], (MAX_HISTORY - 1) * MAX_INPUT_LEN);
        safe_copy(sh->cmds[MAX_HISTORY - 1], MAX_INPUT_LEN, cmd);
    }
    if (sh->count % 25 == 0)          // periodic checkpoint to disk
        save_history_locked();
    sem_post(&sh->lock);
}

static void hist_copy(int idx, char *dst, size_t sz) {
    sem_wait(&sh->lock);
    safe_copy(dst, sz, sh->cmds[idx]);
    sem_post(&sh->lock);
}

// prompt and drawing

static void tab_prompt(Tab *t, char *buf, size_t sz) {
    char shortcwd[64];
    const char *home = get_home();
    if (home && strncmp(t->cwd, home, strlen(home)) == 0)
        snprintf(shortcwd, sizeof(shortcwd), "~%s", t->cwd + strlen(home));
    else
        safe_copy(shortcwd, sizeof(shortcwd), t->cwd);
    snprintf(buf, sz, "user@terminator:%s> ", shortcwd);
}

static void redraw(void) {
    if (am_tab_child || !term.dpy) return;   // tab processes never touch x11
    XClearWindow(term.dpy, term.win);
    XSetForeground(term.dpy, term.gc, BlackPixel(term.dpy, term.screen));
    XFillRectangle(term.dpy, term.win, term.gc, 0, 0, term.width, TAB_BAR_H);
    XSetForeground(term.dpy, term.gc, WhitePixel(term.dpy, term.screen));

    int x = 4;
    for (int i = 0; i < term.ntabs; i++) {
        char label[32];
        snprintf(label, sizeof(label), "[%d]", i + 1);
        if (i == term.active) {
            XSetForeground(term.dpy, term.gc, 0x00AA00);
            XFillRectangle(term.dpy, term.win, term.gc, x - 2, 2, 40, TAB_BAR_H - 4);
            XSetForeground(term.dpy, term.gc, WhitePixel(term.dpy, term.screen));
        }
        XDrawString(term.dpy, term.win, term.gc, x, 16, label, strlen(label));
        x += 44;
    }
    XDrawString(term.dpy, term.win, term.gc, x + 4, 16, "[+]", 3);

    Tab *t = &term.tabs[term.active];
    int max_rows = (term.height - TAB_BAR_H - CHAR_H) / CHAR_H;
    if (max_rows < 1) max_rows = 1;
    int start = 0, top_skip = 0;

    int char_w = 8;
    if (term.font) {
        char_w = term.font->max_bounds.width;
        if (char_w <= 0) char_w = 8;
    }
    int max_chars = (term.width - 8) / char_w;
    if (max_chars < 1) max_chars = 1;

    // nothing is drawn past the window edge: long buffer lines wrap into
    // several rows instead of being clipped on the right
    long total_rows = 0;
    for (int i = 0; i < t->nlines; i++) {
        long l = (long)strlen(t->lines[i]);
        total_rows += l ? (l + max_chars - 1) / max_chars : 1;
    }
    long top_row = total_rows - (long)max_rows - (long)t->scroll;
    if (top_row < 0) top_row = 0;
    long acc = 0;
    while (start < t->nlines) {
        long l = (long)strlen(t->lines[start]);
        long rows = l ? (l + max_chars - 1) / max_chars : 1;
        if (acc + rows > top_row) {
            top_skip = (int)(top_row - acc);
            break;
        }
        acc += rows;
        start++;
    }

    XSetForeground(term.dpy, term.gc, BlackPixel(term.dpy, term.screen));
    int drawn = 0;
    int r = top_skip, i = start;
    while (drawn < max_rows && i < t->nlines) {
        int len = (int)strlen(t->lines[i]);
        int rows = len ? (len + max_chars - 1) / max_chars : 1;
        for (; r < rows && drawn < max_rows; r++, drawn++) {
            int off = r * max_chars;
            int chunk = len - off;
            if (chunk > max_chars) chunk = max_chars;
            if (chunk > 0)
                XDrawString(term.dpy, term.win, term.gc, 4,
                            TAB_BAR_H + (drawn + 1) * CHAR_H,
                            t->lines[i] + off, chunk);
        }
        r = 0;
        i++;
    }

    char prompt[PROMPT_MAX];
    char full[MAX_INPUT_LEN + PROMPT_MAX];

    if (t->searching) {
        snprintf(full, sizeof(full), "Enter search term: %s", t->search_term);
    } else {
        tab_prompt(t, prompt, sizeof(prompt));
        if (t->multiline)
            snprintf(full, sizeof(full), "> %s", t->input);
        else
            snprintf(full, sizeof(full), "%s%s", prompt, t->input);
    }

    int prefix_len = t->searching ? 19 : (t->multiline ? 2 : (int)strlen(prompt));
    int text_len   = t->searching ? (int)strlen(t->search_term) : t->cursor;
    int y = TAB_BAR_H + (drawn + 1) * CHAR_H;

    // horizontal shift: when the line is wider than the window, scroll the
    // view so the cursor stays visible (view_off = chars skipped on the left)
    int total = (int)strlen(full);
    int cur = prefix_len + text_len;
    int view_off = cur - max_chars + 1;
    if (total <= max_chars || view_off < 0) view_off = 0;
    if (total > max_chars && view_off > total - max_chars)
        view_off = total - max_chars;

    int shown = total - view_off;
    if (shown > max_chars) shown = max_chars;
    XDrawString(term.dpy, term.win, term.gc, 4, y, full + view_off, shown);

    int cx = 4 + (cur - view_off) * char_w;
    XDrawLine(term.dpy, term.win, term.gc, cx, y - CHAR_H + 2, cx, y + 2);
    XFlush(term.dpy);
}

// line completeness (quotes, $(), backticks, trailing \)

static int line_incomplete(const char *s, int *ended_quote) {
    int in_single = 0, in_double = 0, depth = 0, backtick = 0;
    for (size_t i = 0; s[i]; i++) {
        char c = s[i];
        if (in_double) {
            if (c == '\\' && s[i + 1]) { i++; continue; }
            if (c == '"') in_double = 0;
            continue;
        }
        if (in_single) {
            if (c == '\'') in_single = 0;
            continue;
        }
        if (c == '\\' && s[i + 1]) { i++; continue; }
        if (c == '\'') in_single = 1;
        else if (c == '"') in_double = 1;
        else if (c == '`') backtick = !backtick;
        else if (c == '$' && s[i + 1] == '(') { depth++; i++; }
        else if (c == ')' && depth > 0) depth--;
    }
    *ended_quote = (in_single || in_double || backtick);
    return in_single || in_double || backtick || depth > 0;
}

// tokenizer with quoting, escapes and globbing

// unescaped token text is copied into this arena, so tokens never alias
// the input line and quoting/escapes can be removed safely.
static char tok_arena[MAX_INPUT_LEN + 8];
static int  tok_off;

// scans one word from *rp into the arena. returns the token start
// (nul-terminated) or null when the next char is a delimiter.
static char *scan_word(char **rp) {
    char *r = *rp;
    while (*r == ' ' || *r == '\t' || *r == '\n') r++;
    if (!*r || *r == '|' || *r == '<' || *r == '>') { *rp = r; return NULL; }
    char *start = tok_arena + tok_off;
    while (*r && *r != ' ' && *r != '\t' && *r != '\n' &&
           *r != '|' && *r != '<' && *r != '>') {
        if (tok_off >= (int)sizeof(tok_arena) - 2) break;
        if (*r == '\'') {                       // literal
            r++;
            while (*r && *r != '\'') tok_arena[tok_off++] = *r++;
            if (*r == '\'') r++;
        } else if (*r == '"') {                 // keep $ ` \ " escapes for us
            r++;
            while (*r && *r != '"') {
                if (*r == '\\' && (r[1] == '"' || r[1] == '\\' ||
                                   r[1] == '$' || r[1] == '`'))
                    r++;
                tok_arena[tok_off++] = *r++;
            }
            if (*r == '"') r++;
        } else if (*r == '\\' && r[1]) {        // \x -> literal x
            r++;
            tok_arena[tok_off++] = *r++;
        } else {
            tok_arena[tok_off++] = *r++;
        }
    }
    tok_arena[tok_off++] = '\0';
    *rp = r;
    return start;
}

// returns number of commands, or -1 on a redirection syntax error.

static int tokenize_pipeline(char *line, char *cmds[][64], int *cmd_argc,
                             int max_cmds, char **redir_in, char **redir_out) {
    *redir_in = *redir_out = NULL;
    int ncmds = 0;
    char *r = line;
    tok_off = 0;

    while (*r && ncmds < max_cmds) {
        while (*r == ' ' || *r == '\t' || *r == '\n') r++;
        if (*r == '|') { r++; continue; }       // tolerate empty command
        if (!*r) break;

        int argc = 0;
        while (*r && *r != '|') {
            while (*r == ' ' || *r == '\t' || *r == '\n') r++;
            if (!*r || *r == '|') break;

            if (*r == '<' || *r == '>') {
                int is_out = (*r == '>');
                r++;
                char *tgt = scan_word(&r);
                if (!tgt || !*tgt) return -1;   // redirect without target
                if (is_out) *redir_out = tgt;
                else        *redir_in  = tgt;
                continue;
            }

            if (argc >= 63) {                   // skip extra tokens
                if (!scan_word(&r)) break;
                continue;
            }

            char *tok = scan_word(&r);
            if (!tok) break;

            if (strchr(tok, '*') || strchr(tok, '?')) {
                glob_t g;
                if (glob(tok, 0, NULL, &g) == 0 && g.gl_pathc > 0) {
                    for (size_t gi = 0; gi < g.gl_pathc && argc < 63; gi++)
                        cmds[ncmds][argc++] = strdup(g.gl_pathv[gi]);
                    globfree(&g);
                } else {
                    cmds[ncmds][argc++] = tok;
                }
            } else {
                cmds[ncmds][argc++] = tok;
            }
        }
        cmds[ncmds][argc] = NULL;
        cmd_argc[ncmds] = argc;
        ncmds++;
        if (*r == '|') r++;
    }
    return ncmds;
}

// splits a command line on top-level ';' (quote/escape aware).

static int split_semicolons(char *s, char *parts[], int max) {
    int n = 0;
    char *p = s;
    int in_s = 0, in_d = 0;
    parts[n++] = s;
    if (n >= max) return n;
    while (*p) {
        if (*p == '\\' && p[1]) { p += 2; continue; }
        if (*p == '\'' && !in_d) in_s = !in_s;
        else if (*p == '"' && !in_s) in_d = !in_d;
        else if (*p == ';' && !in_s && !in_d) {
            *p = '\0';
            parts[n++] = p + 1;
            if (n >= max) return n;
        }
        p++;
    }
    return n;
}

// variable expansion and command substitution

// $?, $name (environment), ~; single quotes stay literal; double quotes
// still expand; backslash pairs are copied verbatim (tokenizer unescapes)
static void expand_variables(char *line, size_t sz, int last_status) {
    char tmp[MAX_INPUT_LEN];
    char *src = line, *dst = tmp;
    int in_single = 0, in_double = 0;

    while (*src && (size_t)(dst - tmp) < sz - 1) {
        if (*src == '\'' && !in_double) {
            in_single = !in_single;
            *dst++ = *src++;
            continue;
        }
        if (*src == '"' && !in_single) {
            in_double = !in_double;
            *dst++ = *src++;
            continue;
        }
        if (*src == '\\' && src[1]) {
            *dst++ = *src++;
            *dst++ = *src++;
            continue;
        }
        if (in_single) { *dst++ = *src++; continue; }

        if (*src == '~' && (src == line || src[-1] == ' ' ||
                            src[-1] == '\t' || src[-1] == '"')) {
            const char *home = get_home();
            if (home) {
                size_t len = strlen(home);
                if ((size_t)(dst - tmp) + len < sz - 1) {
                    memcpy(dst, home, len);
                    dst += len;
                }
            }
            src++;
            continue;
        }
        if (*src == '$' && src[1] == '?') {
            dst += sprintf(dst, "%d", last_status);
            src += 2;
            continue;
        }
        if (*src == '$' && (isalpha((unsigned char)src[1]) || src[1] == '_')) {
            char name[64];
            int ni = 0;
            src++;
            while ((isalnum((unsigned char)*src) || *src == '_') && ni < 63)
                name[ni++] = *src++;
            name[ni] = '\0';
            const char *v = getenv(name);
            if (v) {
                size_t len = strlen(v);
                if ((size_t)(dst - tmp) + len < sz - 1) {
                    memcpy(dst, v, len);
                    dst += len;
                }
            }
            continue;
        }
        *dst++ = *src++;
    }
    *dst = '\0';
    safe_copy(line, sz, tmp);
}

// runs `cmd` through /bin/sh and captures stdout+stderr (trailing \n off).

static int run_and_capture(const char *cmd, char *out, size_t outsz) {
    int pfd[2];
    if (pipe(pfd) < 0) return -1;
    pid_t pid = fork();
    if (pid < 0) { close(pfd[0]); close(pfd[1]); return -1; }
    if (pid == 0) {
        signal(SIGINT, SIG_DFL);
        signal(SIGTSTP, SIG_DFL);
        signal(SIGQUIT, SIG_DFL);
        close(pfd[0]);
        dup2(pfd[1], STDOUT_FILENO);
        dup2(pfd[1], STDERR_FILENO);
        close(pfd[1]);
        execl("/bin/sh", "sh", "-c", cmd, (char *)NULL);
        _exit(127);
    }
    close(pfd[1]);
    size_t total = 0;
    ssize_t n;
    while ((n = read(pfd[0], out + total, outsz - total - 1)) > 0) {
        total += (size_t)n;
        if (total >= outsz - 1) break;
    }
    out[total] = '\0';
    close(pfd[0]);
    waitpid(pid, NULL, 0);
    while (total > 0 && (out[total - 1] == '\n' || out[total - 1] == '\r'))
        out[--total] = '\0';
    return 0;
}

// $(...) and `...` substitution, innermost first, nested and multi-line;
// single-quoted regions are left alone
static void expand_cmdsubst(char *line, size_t sz) {
    int changed = 1;
    while (changed) {
        changed = 0;

        // $(...) pass
        for (char *p = line; *p; ) {
            if (*p == '\\' && p[1]) { p += 2; continue; }
            if (*p == '\'') {                    // skip literal region
                p++;
                while (*p && *p != '\'') p++;
                if (*p) p++;
                continue;
            }
            if (*p == '$' && p[1] == '(') {
                int depth = 0, sq = 0, dq = 0;
                char *q = p + 1;
                while (*q) {
                    if (!sq && !dq && *q == '(') depth++;
                    else if (!sq && !dq && *q == ')') {
                        depth--;
                        if (depth == 0) break;
                    }
                    else if (*q == '\'' && !dq) sq = !sq;
                    else if (*q == '"' && !sq) dq = !dq;
                    q++;
                }
                if (*q != ')') break;            // unclosed: leave as-is
                char inner[2048];
                size_t il = (size_t)(q - (p + 2));
                if (il >= sizeof(inner)) il = sizeof(inner) - 1;
                memcpy(inner, p + 2, il);
                inner[il] = '\0';
                expand_cmdsubst(inner, sizeof(inner));   // innermost first
                char out[4096];
                run_and_capture(inner, out, sizeof(out));
                char nb[MAX_INPUT_LEN];
                size_t pre = (size_t)(p - line);
                size_t olen = strnlen(out, sizeof(out));
                size_t post = strlen(q + 1);
                if (pre + olen + post >= sizeof(nb)) {
                    if (pre + olen >= sizeof(nb)) olen = 0;
                    if (pre + olen + post >= sizeof(nb))
                        post = sizeof(nb) - pre - olen - 1;
                }
                memcpy(nb, line, pre);
                memcpy(nb + pre, out, olen);
                memcpy(nb + pre + olen, q + 1, post);
                nb[pre + olen + post] = '\0';
                safe_copy(line, sz, nb);
                changed = 1;
                break;
            }
            p++;
        }
        if (changed) continue;

        // backtick pass
        for (char *p = line; *p; ) {
            if (*p == '\\' && p[1]) { p += 2; continue; }
            if (*p == '\'') {
                p++;
                while (*p && *p != '\'') p++;
                if (*p) p++;
                continue;
            }
            if (*p == '`') {
                char *q = p + 1;
                while (*q && *q != '`') q++;
                if (*q != '`') break;
                char inner[2048];
                size_t il = (size_t)(q - (p + 1));
                if (il >= sizeof(inner)) il = sizeof(inner) - 1;
                memcpy(inner, p + 1, il);
                inner[il] = '\0';
                expand_cmdsubst(inner, sizeof(inner));
                char out[4096];
                run_and_capture(inner, out, sizeof(out));
                char nb[MAX_INPUT_LEN];
                size_t pre = (size_t)(p - line);
                size_t olen = strnlen(out, sizeof(out));
                size_t post = strlen(q + 1);
                if (pre + olen + post >= sizeof(nb)) {
                    if (pre + olen >= sizeof(nb)) olen = 0;
                    if (pre + olen + post >= sizeof(nb))
                        post = sizeof(nb) - pre - olen - 1;
                }
                memcpy(nb, line, pre);
                memcpy(nb + pre, out, olen);
                memcpy(nb + pre + olen, q + 1, post);
                nb[pre + olen + post] = '\0';
                safe_copy(line, sz, nb);
                changed = 1;
                break;
            }
            p++;
        }
    }
}

// signals

static void sigchld_handler(int sig) {
    (void)sig;
    int saved = errno;
    char b = 1;
    ssize_t r = write(sigchld_wfd, &b, 1);
    (void)r;
    errno = saved;
}

static void setup_signals(void) {
    int pfd[2];
    if (pipe(pfd) == 0) {
        sigchld_rfd = pfd[0];
        sigchld_wfd = pfd[1];
        fcntl(sigchld_rfd, F_SETFL, O_NONBLOCK);
    }
    struct sigaction sa;
    memset(&sa, 0, sizeof(sa));
    sa.sa_handler = sigchld_handler;      // wake select()s on child changes
    sigemptyset(&sa.sa_mask);
    sa.sa_flags = SA_RESTART;             // no sa_nocldstop: we want stops too
    sigaction(SIGCHLD, &sa, NULL);
    // terminator itself must never stop: ctrl+c/ctrl+z are x11 events that
    // we forward with kill() ourselves.
    signal(SIGINT, SIG_IGN);
    signal(SIGTSTP, SIG_IGN);
    signal(SIGQUIT, SIG_IGN);
    signal(SIGPIPE, SIG_IGN);
}

// children must die on ctrl+c etc: undo the inherited "ignore" dispositions

static void reset_child_sigs(void) {
    signal(SIGINT, SIG_DFL);
    signal(SIGTSTP, SIG_DFL);
    signal(SIGQUIT, SIG_DFL);
    signal(SIGCHLD, SIG_DFL);
}

// ends the calling tab backend: a pthread only ends itself, a forked tab
// process exits; the backend's job groups go down with it, like a tab
// process does in process mode

static void tab_backend_exit(void) {
    for (int j = 0; j < tl_njobs; j++)
        if (tl_jobs[j].pgid > 0) kill(-tl_jobs[j].pgid, SIGKILL);
    if (am_tab_thread) {
        if (my_in_fd >= 0) close(my_in_fd);
        if (my_out_fd >= 0) close(my_out_fd);
        if (sigchld_rfd >= 0) close(sigchld_rfd);
        if (sigchld_wfd >= 0) close(sigchld_wfd);
        pthread_exit(NULL);
    }
    _exit(0);
}

// full-screen programs need a real terminal: a capture pipe would get them
// stopped by the tty driver (sigttou/sigttin); they get the controlling
// terminal and its foreground process group

static const char *interactive_cmds[] = {
    "nano", "pico", "vi", "vim", "nvim", "view", "less", "more", "most",
    "top", "htop", "joe", "emacs", "mcedit", NULL
};

static int is_interactive_cmd(const char *cmd) {
    for (int i = 0; interactive_cmds[i]; i++)
        if (strcmp(cmd, interactive_cmds[i]) == 0) return 1;
    return 0;
}

// first word of a saved job line (for fg-resume tty handoff)

static int cmd_is_interactive(const char *line) {
    while (*line == ' ' || *line == '\t') line++;
    char w[64];
    int i = 0;
    while (*line && *line != ' ' && *line != '\t' && i < 63)
        w[i++] = *line++;
    w[i] = '\0';
    return is_interactive_cmd(w);
}

// job control

static void add_job(pid_t pgid, const char *cmd, int status, int cap_fd) {
    if (tl_njobs >= MAX_JOBS) return;
    if (tl_next_job_id < 1) tl_next_job_id = 1;
    Job *j = &tl_jobs[tl_njobs];
    j->pgid = pgid;
    safe_copy(j->cmd, sizeof(j->cmd), cmd);
    j->status = status;
    j->job_id = tl_next_job_id++;
    j->cap_fd = cap_fd;
    tl_njobs++;
}

static void remove_job_at(int idx) {
    if (tl_jobs[idx].cap_fd >= 0) {
        close(tl_jobs[idx].cap_fd);
        tl_jobs[idx].cap_fd = -1;
    }
    for (int k = idx; k < tl_njobs - 1; k++)
        tl_jobs[k] = tl_jobs[k + 1];
    tl_njobs--;
}

// reaps finished background jobs (whole process groups). called from the
// main loop when sigchld fires.
static void cleanup_jobs(void) {
    for (int i = 0; i < tl_njobs; ) {
        Job *j = &tl_jobs[i];
        int empty = 0;
        for (;;) {
            int st;
            pid_t r = waitpid(-j->pgid, &st, WNOHANG | WUNTRACED);
            if (r > 0) {
                if (WIFSTOPPED(st)) j->status = 1;
                continue;
            }
            if (r < 0) empty = 1;      // echild: nobody left in the group
            break;
        }
        if (empty) {
            remove_job_at(i);
            continue;
        }
        i++;
    }
}

// foreground wait: select() over the x11 fd (or gui command pipe), the
// capture pipe and the sigchld self-pipe; ctrl+c/ctrl+z are delivered to
// the foreground process group with kill(); never busy-waits

static int wait_group(Tab *t, pid_t pgid, pid_t leader, int cap_fd_in,
                      int *stopped_out) {
    int cap_fd = cap_fd_in;
    int last_status = 0, leader_status = -1, stopped = 0;
    char buf[4096];

    for (;;) {
        fd_set rf;
        FD_ZERO(&rf);
        int maxfd = sigchld_rfd;
        if (sigchld_rfd >= 0) FD_SET(sigchld_rfd, &rf);
        if (maxfd < 0) maxfd = 0;

        if (cap_fd >= 0) {
            FD_SET(cap_fd, &rf);
            if (cap_fd > maxfd) maxfd = cap_fd;
        }
        if (!am_tab_child && term.dpy) {
            int xfd = ConnectionNumber(term.dpy);
            FD_SET(xfd, &rf);
            if (xfd > maxfd) maxfd = xfd;
        } else if (am_tab_child && my_in_fd >= 0) {
            FD_SET(my_in_fd, &rf);
            if (my_in_fd > maxfd) maxfd = my_in_fd;
        }

        // bounded tick: in thread mode a sigchld wakeup can be drained by
        // another backend's thread - the waitpid below reaps regardless
        struct timeval tv = {0, 50000};
        if (select(maxfd + 1, &rf, NULL, NULL, &tv) < 0) {
            if (errno == EINTR) continue;
            break;
        }

        if (cap_fd >= 0 && FD_ISSET(cap_fd, &rf)) {
            ssize_t n = read(cap_fd, buf, sizeof(buf) - 1);
            if (n > 0) {
                buf[n] = '\0';
                tab_append(t, buf);
                redraw();
            } else if (n == 0 || (errno != EINTR && errno != EAGAIN)) {
                close(cap_fd);
                cap_fd = -1;                    // writers done; keep waiting
            }
        }

        if (!am_tab_child && term.dpy && FD_ISSET(ConnectionNumber(term.dpy), &rf)) {
            // this wait belongs to tab 'owner'; while the job runs the gui
            // stays usable: tabs can be switched, other tabs can type and
            // queue lines, and ctrl+c/ctrl+z only hit this job when
            // pressed in this tab
            int owner = (int)(t - term.tabs);
            while (XPending(term.dpy)) {
                XEvent ev;
                XNextEvent(term.dpy, &ev);
                if (ev.type == KeyPress) {
                    char kb[32];
                    KeySym ks;
                    int klen = XLookupString(&ev.xkey, kb, sizeof(kb), &ks, NULL);
                    if (ks >= XK_A && ks <= XK_Z) ks += XK_a - XK_A;
                    int m = 0;
                    if (ev.xkey.state & ControlMask) m |= MOD_CTRL;
                    if (ev.xkey.state & ShiftMask)   m |= MOD_SHIFT;
                    if (ev.xkey.state & Mod1Mask)    m |= MOD_ALT;
                    Tab *at = &term.tabs[term.active];

                    if (m == MOD_CTRL && ks == XK_c) {
                        if (term.active == owner) {
                            kill(-pgid, SIGINT);
                            tab_append(t, "^C\n");
                        } else {
                            // ctrl+c in another tab: clear only that tab's input,
                            // never the running job
                            at->input_len = at->cursor = 0;
                            at->input[0] = 0;
                            at->multiline = 0;
                            at->pending[0] = 0;
                            at->pend_sep[0] = 0;
                            at->completing = 0;
                            tab_append(at, "^C\n");
                        }
                    } else if (m == MOD_CTRL && ks == XK_z) {
                        if (term.active == owner) {
                            kill(-pgid, SIGTSTP);
                        } else if (at->fg_busy) {
                            // this tab's command is only queued so far:
                            // ctrl+z here drops it from the queue and
                            // unblocks the tab; the running job keeps going
                            int mt = (int)(at - term.tabs);
                            for (int k = 0; k < gui_npend; k++) {
                                if (gui_pend_tab[k] == mt) {
                                    for (int q = k; q < gui_npend - 1; q++) {
                                        gui_pend_tab[q] = gui_pend_tab[q + 1];
                                        memcpy(gui_pend_cmd[q],
                                               gui_pend_cmd[q + 1],
                                               MAX_INPUT_LEN);
                                    }
                                    gui_npend--;
                                    break;
                                }
                            }
                            at->fg_busy = 0;
                            tab_append(at, "^Z\n");
                        }
                    } else if (m == MOD_CTRL && ks == XK_s) {
                        if (term.ntabs > 1)
                            term.active = (term.active + 1) % term.ntabs;
                    } else if (m == MOD_CTRL && ks == XK_r) {
                        at->searching = 1;
                        at->search_term[0] = 0;
                    } else if (m == MOD_CTRL && ks == XK_t) {
                        new_tab();
                    } else if (at->searching) {
                        if (ks == XK_Return || ks == XK_KP_Enter) {
                            do_hist_search(at);
                        } else if (ks == XK_Escape) {
                            at->searching = 0;
                            at->search_term[0] = 0;
                        } else if (ks == XK_BackSpace || ks == XK_Delete) {
                            size_t sl = strlen(at->search_term);
                            if (sl > 0) at->search_term[sl - 1] = 0;
                        } else if (klen == 1 && isprint((unsigned char)kb[0]) &&
                                   strlen(at->search_term) <
                                       sizeof(at->search_term) - 1) {
                            size_t sl = strlen(at->search_term);
                            at->search_term[sl] = kb[0];
                            at->search_term[sl + 1] = 0;
                        }
                    } else if (ks == XK_Return || ks == XK_KP_Enter) {
                        // the tab running this job takes no input; a line
                        // typed in another tab is echoed and queued there
                        // until that tab can run it - from that moment that
                        // tab takes no input either
                        if (term.active != owner && !at->fg_busy) {
                        char prompt[PROMPT_MAX];
                        char echo[MAX_INPUT_LEN + PROMPT_MAX];
                        tab_prompt(at, prompt, sizeof(prompt));
                        if (at->multiline)
                            snprintf(echo, sizeof(echo), "> %s\n", at->input);
                        else
                            snprintf(echo, sizeof(echo), "%s%s\n",
                                     prompt, at->input);
                        tab_append(at, echo);

                        char joined[MAX_INPUT_LEN];
                        if (at->multiline)
                            snprintf(joined, sizeof(joined), "%s%s%s",
                                     at->pending, at->pend_sep, at->input);
                        else
                            safe_copy(joined, sizeof(joined), at->input);
                        at->multiline = 0;
                        at->pending[0] = 0;
                        at->pend_sep[0] = 0;
                        at->input_len = at->cursor = 0;
                        at->input[0] = 0;
                        at->hist_idx = -1;
                        at->completing = 0;
                        if (joined[0] && gui_npend < 8) {
                            gui_pend_tab[gui_npend] = (int)(at - term.tabs);
                            safe_copy(gui_pend_cmd[gui_npend],
                                      MAX_INPUT_LEN, joined);
                            gui_npend++;
                            at->fg_busy = 1;   // cleared once it ran
                        }
                        }
                    } else if (ks == XK_BackSpace || ks == XK_Delete) {
                        if (term.active != owner && !at->fg_busy &&
                            at->cursor > 0) {
                            memmove(at->input + at->cursor - 1,
                                    at->input + at->cursor,
                                    (size_t)(at->input_len - at->cursor + 1));
                            at->input_len--;
                            at->cursor--;
                        }
                    } else if (klen == 1 && isprint((unsigned char)kb[0])) {
                        if (term.active != owner && !at->fg_busy)
                            input_insert(at, kb, 1);
                    }
                    redraw();
                } else if (ev.type == ButtonPress &&
                           ev.xbutton.y < TAB_BAR_H) {
                    int idx = (ev.xbutton.x - 4) / 44;
                    if (idx >= 0 && idx < term.ntabs) term.active = idx;
                    else if (idx == term.ntabs) new_tab();
                    redraw();
                } else if (ev.type == Expose && ev.xexpose.count == 0) {
                    redraw();
                }
            }
        } else if (am_tab_child && my_in_fd >= 0 && FD_ISSET(my_in_fd, &rf)) {
            char type;
            char pl[MAX_INPUT_LEN];
            size_t plen;
            if (read_frame(my_in_fd, &type, pl, sizeof(pl) - 1, &plen) > 0) {
                if (type == 'I') {
                    if (tl_fg_running) {
                        kill(-pgid, SIGINT);
                        tab_append(t, "^C\n");
                    }
                } else if (type == 'Z') {
                    if (tl_fg_running) kill(-pgid, SIGTSTP);
                } else if (type == 'L') {
                    if (child_npend < 8)
                        safe_copy(child_pend[child_npend++], MAX_INPUT_LEN, pl);
                }
            } else {
                tab_backend_exit();             // gui went away
            }
        }

        if (sigchld_rfd >= 0 && FD_ISSET(sigchld_rfd, &rf)) {
            char db[64];
            while (read(sigchld_rfd, db, sizeof(db)) > 0) {}
        }

        int empty = 0;
        for (;;) {
            int st;
            pid_t r = waitpid(-pgid, &st, WNOHANG | WUNTRACED);
            if (r > 0) {
                if (WIFSTOPPED(st)) {
                    stopped = 1;
                } else {
                    int code = WIFEXITED(st) ? WEXITSTATUS(st)
                                             : 128 + WTERMSIG(st);
                    last_status = code;
                    if (r == leader) leader_status = code;
                }
                continue;
            }
            if (r < 0) empty = 1;
            break;
        }
        if (stopped || empty) break;
    }

    if (cap_fd >= 0) close(cap_fd);
    *stopped_out = stopped;
    return leader_status >= 0 ? leader_status : last_status;
}

// pipelines with redirection

static int run_pipeline(Tab *t, char *cmdline, int background) {
    char *cmds[MAX_PIPELINE][64];
    int cmd_argc[MAX_PIPELINE];
    char *rin = NULL, *rout = NULL;

    char copy[MAX_INPUT_LEN];
    safe_copy(copy, sizeof(copy), cmdline);

    int ncmds = tokenize_pipeline(copy, cmds, cmd_argc, MAX_PIPELINE,
                                  &rin, &rout);
    if (ncmds < 0) {
        tab_append(t, "terminator: syntax error near unexpected token\n");
        t->last_status = 2;
        return 2;
    }
    if (ncmds == 0) return 0;

    // report a missing input file instead of running the command
    if (rin && access(rin, F_OK) != 0) {
        char err[PATH_MAX + 64];
        snprintf(err, sizeof(err),
                 "terminator: %s: no such file or directory\n", rin);
        tab_append(t, err);
        t->last_status = 1;
        return 1;
    }

    int pipes[MAX_PIPELINE][2];
    for (int i = 0; i < ncmds - 1; i++) {
        if (pipe(pipes[i]) < 0) {
            tab_append(t, "terminator: pipe failed\n");
            return 1;
        }
    }

    int outpipe[2] = {-1, -1};
        // full-screen programs (nano, vim, less, top, ...) get the real terminal
        // instead of a capture pipe, otherwise the tty driver stops them
    int interactive = (ncmds == 1 && !rin && !rout && !background &&
                       cmds[0][0] && is_interactive_cmd(cmds[0][0]));
    int capture = !rout && !interactive;
    if (capture && pipe(outpipe) < 0) {
        tab_append(t, "terminator: pipe failed\n");
        for (int i = 0; i < ncmds - 1; i++) {
            close(pipes[i][0]);
            close(pipes[i][1]);
        }
        return 1;
    }

    pid_t pids[MAX_PIPELINE];
    for (int i = 0; i < ncmds; i++) {
        pids[i] = fork();
        if (pids[i] < 0) {
            tab_append(t, "terminator: fork failed\n");
            return 1;
        }
        if (pids[i] == 0) {
            reset_child_sigs();
            if (i == 0) setpgid(0, 0);
            else        setpgid(0, pids[0]);
            if (chdir(t->cwd) != 0) { /* anchored at the tab's directory */ }

            if (interactive) {
                // editors/pagers need the real terminal on fd 0/1/2
                int ttyfd = open("/dev/tty", O_RDWR);
                if (ttyfd < 0) {
                    dprintf(2, "terminator: %s: needs a terminal - start "
                               "terminator from a terminal window\n", cmds[0][0]);
                    _exit(126);
                }
                dup2(ttyfd, STDIN_FILENO);
                dup2(ttyfd, STDOUT_FILENO);
                dup2(ttyfd, STDERR_FILENO);
                if (ttyfd > STDERR_FILENO) close(ttyfd);
            }

            if (i > 0) {
                dup2(pipes[i - 1][0], STDIN_FILENO);
            } else if (rin) {
                int fd = open(rin, O_RDONLY);
                if (fd < 0) {
                    dprintf(2, "terminator: %s: no such file or directory\n", rin);
                    _exit(1);
                }
                dup2(fd, STDIN_FILENO);
                close(fd);
            }

            if (i < ncmds - 1) {
                dup2(pipes[i][1], STDOUT_FILENO);
            } else if (rout) {
                int fd = open(rout, O_WRONLY | O_CREAT | O_TRUNC, 0644);
                if (fd < 0) {
                    dprintf(2, "terminator: cannot open %s\n", rout);
                    _exit(1);
                }
                dup2(fd, STDOUT_FILENO);
                close(fd);
            } else if (capture) {
                dup2(outpipe[1], STDOUT_FILENO);
                dup2(outpipe[1], STDERR_FILENO);
            }

            for (int j = 0; j < ncmds - 1; j++) {
                close(pipes[j][0]);
                close(pipes[j][1]);
            }
            if (capture) {
                close(outpipe[0]);
                close(outpipe[1]);
            }

            execvp(cmds[i][0], cmds[i]);
            dprintf(2, "terminator: %s: %s\n", cmds[i][0],
                    errno == ENOENT ? "command not found" : strerror(errno));
            _exit(errno == ENOENT ? 127 : 126);
        }
    }

    for (int i = 0; i < ncmds - 1; i++) {
        close(pipes[i][0]);
        close(pipes[i][1]);
    }

    // close the setpgid race: parent also moves children into the group
    setpgid(pids[0], pids[0]);
    for (int i = 1; i < ncmds; i++)
        setpgid(pids[i], pids[0]);
    pid_t pgid = pids[0];

    if (background) {
        int cap = -1;
        if (capture) {
            close(outpipe[1]);
            cap = outpipe[0];            // drained by the main loop
        }
        add_job(pgid, cmdline, 0, cap);
        char msg[128];
        snprintf(msg, sizeof(msg), "[%d] %d\n",
                 tl_jobs[tl_njobs - 1].job_id, (int)pgid);
        tab_append(t, msg);
        t->last_status = 0;
        return 0;
    }

    if (capture) close(outpipe[1]);

    // make the child's process group the foreground group of the
    // controlling terminal so it is not stopped when it touches the tty
    int tty_ctrl = -1;
    pid_t fg_saved = 0;
    if (interactive) {
        tty_ctrl = open("/dev/tty", O_RDWR);
        if (tty_ctrl >= 0) {
            signal(SIGTTOU, SIG_IGN);
            fg_saved = tcgetpgrp(tty_ctrl);
            if (fg_saved < 0) fg_saved = 0;
            tcsetpgrp(tty_ctrl, pgid);
            // the program draws on the terminal that started terminator,
            // not in our window - say so, or the silent tab looks frozen
            char note[300];
            snprintf(note, sizeof(note),
                     "%s: full-screen program running on the terminal that "
                     "started terminator - use it there; ctrl+z suspends it "
                     "and brings the prompt back\n", cmds[0][0]);
            tab_append(t, note);
        }
    }

    tl_fg_pgid = pgid;
    tl_fg_running = 1;

    int stopped = 0;
    int status = wait_group(t, pgid, pids[0], capture ? outpipe[0] : -1,
                            &stopped);

    tl_fg_running = 0;
    tl_fg_pgid = 0;

    if (tty_ctrl >= 0) {              // take the terminal back
        tcsetpgrp(tty_ctrl, fg_saved ? fg_saved : getpgrp());
        close(tty_ctrl);
    }

    if (stopped) {
        add_job(pgid, cmdline, 1, -1);
        char msg[600];
        snprintf(msg, sizeof(msg), "[%d]+  Stopped\t\t%.400s\n",
                 tl_jobs[tl_njobs - 1].job_id, cmdline);
        tab_append(t, msg);
        status = 1;
    }

    t->last_status = status;
    return status;
}

// multiwatch: all commands run in parallel, one supervisor process and one
// pipe per command; the parent select()s on every read end and on the x11
// connection; a supervisor re-runs its command 2 s after it finishes;
// ctrl+c kills every supervisor group

static void run_multiWatch(Tab *t, char *cmdline) {
    char *p = strchr(cmdline, '[');
    if (!p) {
        tab_append(t, "multiwatch: usage multiWatch [\"cmd1\", \"cmd2\", ...]\n");
        return;
    }
    p++;
    char cmds[16][256];
    int n = 0;
    while (*p && n < 16) {
        while (*p == ' ' || *p == ',' || *p == '"') p++;
        if (*p == ']') break;
        char *start = p;
        while (*p && *p != '"' && *p != ']') p++;
        size_t len = (size_t)(p - start);
        if (len >= sizeof(cmds[0])) len = sizeof(cmds[0]) - 1;
        memcpy(cmds[n], start, len);
        cmds[n][len] = '\0';
        n++;
        if (*p == '"') p++;
        while (*p == ' ' || *p == ',') p++;
    }
    if (n == 0) return;

    int pfd[16][2];
    pid_t sup[16];
    int started = 0;

    for (int i = 0; i < n; i++) {
        if (pipe(pfd[i]) < 0) break;
        pid_t pid = fork();
        if (pid < 0) {
            close(pfd[i][0]);
            close(pfd[i][1]);
            pfd[i][0] = pfd[i][1] = -1;
            break;
        }
        if (pid == 0) {
            // supervisor: keeps re-running the command every 2 s
            reset_child_sigs();
            setpgid(0, 0);
            close(pfd[i][0]);
            int wfd = pfd[i][1];
            for (int k = 0; k < i; k++) {
                if (pfd[k][0] >= 0) { close(pfd[k][0]); close(pfd[k][1]); }
            }
            for (;;) {
                char hdr[512];
                snprintf(hdr, sizeof(hdr), "\"%.200s\", %ld:\n" MW_DASHES "\n",
                         cmds[i], (long)time(NULL));
                if (write(wfd, hdr, strlen(hdr)) < 0) _exit(0);
                pid_t g = fork();
                if (g == 0) {
                    dup2(wfd, STDOUT_FILENO);
                    dup2(wfd, STDERR_FILENO);
                    close(wfd);
                    if (chdir(t->cwd) != 0) { /* ignore */ }
                    execl("/bin/sh", "sh", "-c", cmds[i], (char *)NULL);
                    _exit(127);
                }
                int st;
                waitpid(g, &st, 0);
                const char *foot = MW_DASHES "\n";
                if (write(wfd, foot, strlen(foot)) < 0) _exit(0);
                sleep(2);
            }
        }
        sup[i] = pid;
        close(pfd[i][1]);
        pfd[i][1] = -1;
        started++;
    }
    if (started == 0) return;

    int open_cnt = started;
    while (open_cnt > 0) {
        fd_set rf;
        FD_ZERO(&rf);
        int maxfd = sigchld_rfd;
        if (sigchld_rfd >= 0) FD_SET(sigchld_rfd, &rf);
        if (maxfd < 0) maxfd = 0;

        for (int i = 0; i < n; i++) {
            if (pfd[i][0] >= 0) {
                FD_SET(pfd[i][0], &rf);
                if (pfd[i][0] > maxfd) maxfd = pfd[i][0];
            }
        }
        if (!am_tab_child && term.dpy) {
            int xfd = ConnectionNumber(term.dpy);
            FD_SET(xfd, &rf);
            if (xfd > maxfd) maxfd = xfd;
        } else if (am_tab_child && my_in_fd >= 0) {
            FD_SET(my_in_fd, &rf);
            if (my_in_fd > maxfd) maxfd = my_in_fd;
        }

        if (select(maxfd + 1, &rf, NULL, NULL, NULL) < 0) {
            if (errno == EINTR) continue;
            break;
        }

        int stop = 0;
        if (!am_tab_child && term.dpy && FD_ISSET(ConnectionNumber(term.dpy), &rf)) {
            while (XPending(term.dpy)) {
                XEvent ev;
                XNextEvent(term.dpy, &ev);
                if (ev.type == KeyPress) {
                    KeySym ks;
                    XLookupString(&ev.xkey, NULL, 0, &ks, NULL);
                    if ((ev.xkey.state & ControlMask) &&
                        (ks == XK_c || ks == XK_C))
                        stop = 1;
                } else if (ev.type == Expose && ev.xexpose.count == 0) {
                    redraw();
                }
            }
        } else if (am_tab_child && my_in_fd >= 0 && FD_ISSET(my_in_fd, &rf)) {
            char type;
            char pl[MAX_INPUT_LEN];
            size_t plen;
            if (read_frame(my_in_fd, &type, pl, sizeof(pl) - 1, &plen) > 0) {
                if (type == 'I') stop = 1;
                else if (type == 'L') {
                    if (child_npend < 8)
                        safe_copy(child_pend[child_npend++], MAX_INPUT_LEN, pl);
                }
            } else {
                tab_backend_exit();            // gui went away
            }
        }

        for (int i = 0; i < n; i++) {
            if (pfd[i][0] >= 0 && FD_ISSET(pfd[i][0], &rf)) {
                char buf[4096];
                ssize_t nn = read(pfd[i][0], buf, sizeof(buf) - 1);
                if (nn > 0) {
                    buf[nn] = '\0';
                    tab_append(t, buf);
                    redraw();
                } else if (nn == 0) {
                    close(pfd[i][0]);
                    pfd[i][0] = -1;
                    open_cnt--;
                }
            }
        }

        if (sigchld_rfd >= 0 && FD_ISSET(sigchld_rfd, &rf)) {
            char db[64];
            while (read(sigchld_rfd, db, sizeof(db)) > 0) {}
        }

        if (stop) {
            for (int i = 0; i < n; i++) {
                if (sup[i] > 0) {
                    kill(-sup[i], SIGKILL);      // supervisor + its child
                    kill(sup[i], SIGKILL);
                }
            }
            tab_append(t, "^C\n");
            break;
        }
    }

    for (int i = 0; i < n; i++) {
        if (pfd[i][0] >= 0) close(pfd[i][0]);
        if (sup[i] > 0) {
            kill(-sup[i], SIGKILL);
            waitpid(sup[i], NULL, 0);
        }
    }
    redraw();
}

// [ ... ] tests

static int eval_test(char *expr) {
    while (*expr == ' ' || *expr == '\t' || *expr == '[') expr++;
    char *end = expr + strlen(expr) - 1;
    while (end > expr && (*end == ' ' || *end == '\t' || *end == ']')) {
        *end = '\0';
        end--;
    }

    char *args[8];
    int argc = 0;
    char *p = expr;

    while (*p && argc < 7) {
        while (*p == ' ' || *p == '\t') p++;
        if (!*p) break;
        if (*p == '"' || *p == '\'') {
            char q = *p++;
            args[argc++] = p;
            while (*p && *p != q) p++;
            if (*p) *p++ = '\0';
        } else {
            args[argc++] = p;
            while (*p && *p != ' ' && *p != '\t') p++;
            if (*p) *p++ = '\0';
        }
    }
    if (argc == 0) return 0;
    if (argc == 1) return args[0][0] != '\0';

    if (argc == 2) {
        if (strcmp(args[0], "-f") == 0) return access(args[1], F_OK) == 0;
        if (strcmp(args[0], "-d") == 0) {
            struct stat st;
            return stat(args[1], &st) == 0 && S_ISDIR(st.st_mode);
        }
        if (strcmp(args[0], "-e") == 0) return access(args[1], F_OK) == 0;
        if (strcmp(args[0], "-r") == 0) return access(args[1], R_OK) == 0;
        if (strcmp(args[0], "-w") == 0) return access(args[1], W_OK) == 0;
        if (strcmp(args[0], "-x") == 0) return access(args[1], X_OK) == 0;
        if (strcmp(args[0], "-s") == 0) {
            struct stat st;
            return stat(args[1], &st) == 0 && st.st_size > 0;
        }
        if (strcmp(args[0], "-z") == 0) return args[1][0] == '\0';
        if (strcmp(args[0], "-n") == 0) return args[1][0] != '\0';
        return 0;
    }

    if (argc == 3) {
        if (strcmp(args[1], "=")  == 0)  return strcmp(args[0], args[2]) == 0;
        if (strcmp(args[1], "!=") == 0)  return strcmp(args[0], args[2]) != 0;
        if (strcmp(args[1], "-eq") == 0) return atoi(args[0]) == atoi(args[2]);
        if (strcmp(args[1], "-ne") == 0) return atoi(args[0]) != atoi(args[2]);
        if (strcmp(args[1], "-gt") == 0) return atoi(args[0]) >  atoi(args[2]);
        if (strcmp(args[1], "-ge") == 0) return atoi(args[0]) >= atoi(args[2]);
        if (strcmp(args[1], "-lt") == 0) return atoi(args[0]) <  atoi(args[2]);
        if (strcmp(args[1], "-le") == 0) return atoi(args[0]) <= atoi(args[2]);
    }
    return 0;
}

// script helpers

static FILE *tab_fopen(Tab *t, const char *path, const char *mode) {
    if (path[0] == '/') return fopen(path, mode);
    char buf[PATH_MAX * 2];
    snprintf(buf, sizeof(buf), "%s/%s", t->cwd, path);
    return fopen(buf, mode);
}

// quote-aware: cuts a trailing " # comment"

static void strip_comment(char *s) {
    int in_s = 0, in_d = 0;
    for (char *p = s; *p; p++) {
        if (*p == '\\' && p[1] && !in_s) { p++; continue; }
        if (*p == '\'' && !in_d) in_s = !in_s;
        else if (*p == '"' && !in_s) in_d = !in_d;
        else if (*p == '#' && !in_s && !in_d &&
                 (p == s || p[-1] == ' ' || p[-1] == '\t')) {
            *p = '\0';
            return;
        }
    }
}

// true when the line ends with "; then" (only spaces after)

static int line_ends_with_then(const char *p) {
    const char *q = p;
    while ((q = strstr(q, "; then")) != NULL) {
        const char *r = q + 6;
        while (*r == ' ' || *r == '\t') r++;
        if (*r == '\0') return 1;
        q++;
    }
    return 0;
}

static void strip_then_suffix(char *p) {
    char *q = p;
    while ((q = strstr(q, "; then")) != NULL) {
        char *r = q + 6;
        while (*r == ' ' || *r == '\t') r++;
        if (*r == '\0') { *q = '\0'; return; }
        q++;
    }
}

static int bare_word(const char *p, const char *w) {
    size_t l = strlen(w);
    if (strncmp(p, w, l) != 0) return 0;
    p += l;
    while (*p == ' ' || *p == '\t') p++;
    return *p == '\0';
}

// syntax pre-scan: every if needs a matching fi (nesting aware), then/else
// must be in place. the script is not run when this fails.
static int script_check(Tab *t, char (*lines)[MAX_INPUT_LEN], int n,
                        const char *filename) {
    int depth = 0;
    int have_then[64];
    int ifline[64];
    char err[MAX_INPUT_LEN + 128];

    for (int i = 0; i < n; i++) {
        char *p = lines[i];
        while (*p == ' ' || *p == '\t') p++;
        if (*p == '#' || *p == '\0') continue;

        char w[32];
        int wi = 0;
        while (p[wi] && p[wi] != ' ' && p[wi] != '\t' && wi < 31) {
            w[wi] = p[wi];
            wi++;
        }
        w[wi] = '\0';

        if (strcmp(w, "if") == 0) {
            if (depth >= 64) {
                snprintf(err, sizeof(err),
                         "terminator: %s: line %d: syntax error: "
                         "if nesting too deep\n", filename, i + 1);
                tab_append(t, err);
                return 0;
            }
            ifline[depth] = i + 1;
            have_then[depth] = line_ends_with_then(p);
            depth++;
        } else if (strcmp(w, "elif") == 0) {
            if (depth == 0) {
                snprintf(err, sizeof(err),
                         "terminator: %s: line %d: syntax error: "
                         "unexpected elif\n", filename, i + 1);
                tab_append(t, err);
                return 0;
            }
            have_then[depth - 1] = line_ends_with_then(p);
        } else if (strcmp(w, "else") == 0) {
            if (depth == 0) {
                snprintf(err, sizeof(err),
                         "terminator: %s: line %d: syntax error: "
                         "unexpected else\n", filename, i + 1);
                tab_append(t, err);
                return 0;
            }
            if (!have_then[depth - 1]) {
                snprintf(err, sizeof(err),
                         "terminator: %s: line %d: syntax error: "
                         "else without then (if at line %d)\n",
                         filename, i + 1, ifline[depth - 1]);
                tab_append(t, err);
                return 0;
            }
            have_then[depth - 1] = 1;
        } else if (strcmp(w, "then") == 0 && bare_word(p, "then")) {
            if (depth == 0) {
                snprintf(err, sizeof(err),
                         "terminator: %s: line %d: syntax error: "
                         "unexpected then\n", filename, i + 1);
                tab_append(t, err);
                return 0;
            }
            have_then[depth - 1] = 1;
        } else if (strcmp(w, "fi") == 0) {
            if (depth == 0) {
                snprintf(err, sizeof(err),
                         "terminator: %s: line %d: syntax error: "
                         "unexpected fi\n", filename, i + 1);
                tab_append(t, err);
                return 0;
            }
            if (!have_then[depth - 1]) {
                snprintf(err, sizeof(err),
                         "terminator: %s: line %d: syntax error: "
                         "missing then for if at line %d\n",
                         filename, i + 1, ifline[depth - 1]);
                tab_append(t, err);
                return 0;
            }
            depth--;
        }
    }
    if (depth > 0) {
        snprintf(err, sizeof(err),
                 "terminator: %s: syntax error: missing fi "
                 "for if at line %d\n", filename, ifline[depth - 1]);
        tab_append(t, err);
        return 0;
    }
    return 1;
}

// expands $1..$9, $#, $?, script variables and the environment into `out`.

static void script_expand(Tab *t, char *line, char *out, size_t sz,
                          char **args, int argc, int nvars,
                          char vars[][2][128]) {
    char *src = line, *dst = out;

    while (*src && (size_t)(dst - out) < sz - 1) {
        if (*src == '$') {
            if (src[1] == '?') {
                dst += sprintf(dst, "%d", t->last_status);
                src += 2;
                continue;
            }
            if (src[1] == '#') {
                dst += sprintf(dst, "%d", argc > 0 ? argc - 1 : 0);
                src += 2;
                continue;
            }
            if (isdigit((unsigned char)src[1])) {
                int idx = src[1] - '0';
                if (idx >= 1 && idx < argc) {
                    size_t l = strlen(args[idx]);
                    memcpy(dst, args[idx], l);
                    dst += l;
                }
                src += 2;
                continue;
            }
            if (isalpha((unsigned char)src[1]) || src[1] == '_') {
                char name[64];
                int ni = 0;
                src++;
                while ((isalnum((unsigned char)*src) || *src == '_') && ni < 63)
                    name[ni++] = *src++;
                name[ni] = '\0';
                int found = 0;
                for (int v = 0; v < nvars; v++) {
                    if (strcmp(vars[v][0], name) == 0) {
                        size_t l = strlen(vars[v][1]);
                        memcpy(dst, vars[v][1], l);
                        dst += l;
                        found = 1;
                        break;
                    }
                }
                if (!found) {
                    const char *ev = getenv(name);
                    if (ev) {
                        size_t l = strlen(ev);
                        memcpy(dst, ev, l);
                        dst += l;
                    }
                }
                continue;
            }
            *dst++ = *src++;                 // lone $ stays
            continue;
        }
        *dst++ = *src++;
    }
    *dst = '\0';
}

// interprets a bash script itself (never /bin/bash): comments, multiple
// commands, pipes, redirection, command substitution, variables, $1..$9,
// $#, $?, nested if/elif/else/fi with [ ... ] tests, exit [n]; syntax
// errors are reported before anything runs
static void run_script(Tab *t, const char *filename, char **args, int argc) {
    FILE *f = tab_fopen(t, filename, "r");
    if (!f) {
        char err[PATH_MAX + 64];
        snprintf(err, sizeof(err),
                 "terminator: %s: no such file or directory\n", filename);
        tab_append(t, err);
        t->last_status = 127;
        return;
    }

    int cap = 128, n = 0;
    char (*lines)[MAX_INPUT_LEN] = malloc(cap * MAX_INPUT_LEN);
    if (!lines) { fclose(f); return; }
    char rbuf[MAX_INPUT_LEN];
    while (fgets(rbuf, sizeof(rbuf), f)) {
        rbuf[strcspn(rbuf, "\r\n")] = '\0';
        if (n == cap) {
            cap *= 2;
            char (*nl)[MAX_INPUT_LEN] = realloc(lines, cap * MAX_INPUT_LEN);
            if (!nl) break;
            lines = nl;
        }
        safe_copy(lines[n++], MAX_INPUT_LEN, rbuf);
    }
    fclose(f);

    if (!script_check(t, lines, n, filename)) {
        free(lines);
        t->last_status = 2;
        return;
    }

    char vars[32][2][128];
    int nvars = 0;
    struct { int active, taken; } stk[64];
    int depth = 0;
    int quit = 0;

    for (int i = 0; i < n && !quit; i++) {
        char *p = lines[i];
        while (*p == ' ' || *p == '\t') p++;
        strip_comment(p);
        while (*p == ' ' || *p == '\t') p++;
        if (!*p) continue;

        char e[MAX_INPUT_LEN];
        script_expand(t, p, e, sizeof(e), args, argc, nvars, vars);

        char *ep = e;
        while (*ep == ' ' || *ep == '\t') ep++;
        size_t elen = strlen(ep);
        while (elen > 0 && (ep[elen - 1] == ' ' || ep[elen - 1] == '\t'))
            ep[--elen] = '\0';
        if (!*ep) continue;

        if (strncmp(ep, "if", 2) == 0 && (ep[2] == ' ' || ep[2] == '\t' || ep[2] == '\0')) {
            if (depth < 64) {
                char cond[MAX_INPUT_LEN];
                safe_copy(cond, sizeof(cond), ep + 2);
                strip_then_suffix(cond);
                int v = eval_test(cond);
                stk[depth].active = v;
                stk[depth].taken = v;
                depth++;
            }
            continue;
        }
        if (strncmp(ep, "elif", 4) == 0 && (ep[4] == ' ' || ep[4] == '\t' || ep[4] == '\0')) {
            if (depth > 0) {
                char cond[MAX_INPUT_LEN];
                safe_copy(cond, sizeof(cond), ep + 4);
                strip_then_suffix(cond);
                int v = eval_test(cond);
                stk[depth - 1].active = !stk[depth - 1].taken && v;
                if (stk[depth - 1].active) stk[depth - 1].taken = 1;
            }
            continue;
        }
        if (bare_word(ep, "else")) {
            if (depth > 0) {
                stk[depth - 1].active = !stk[depth - 1].taken;
                if (stk[depth - 1].active) stk[depth - 1].taken = 1;
            }
            continue;
        }
        if (bare_word(ep, "then")) continue;
        if (bare_word(ep, "fi")) {
            if (depth > 0) depth--;
            continue;
        }

        int all_active = 1;
        for (int k = 0; k < depth; k++)
            if (!stk[k].active) all_active = 0;
        if (!all_active) continue;

        // exit [n]
        if (strcmp(ep, "exit") == 0 || strncmp(ep, "exit ", 5) == 0 ||
            strncmp(ep, "exit\t", 5) == 0) {
            t->last_status = strncmp(ep, "exit", 4) == 0 && ep[4] ? atoi(ep + 4) : 0;
            quit = 1;
            continue;
        }

        // name=value (quotes around the value are stripped)
        {
            char *eq = strchr(ep, '=');
            if (eq && eq != ep &&
                (isalpha((unsigned char)ep[0]) || ep[0] == '_')) {
                int ok = 1;
                for (char *c = ep; c < eq; c++)
                    if (!(isalnum((unsigned char)*c) || *c == '_')) { ok = 0; break; }
                if (ok) {
                    *eq = '\0';
                    char *val = eq + 1;
                    size_t vl = strlen(val);
                    if (vl >= 2 && ((val[0] == '"' && val[vl - 1] == '"') ||
                                    (val[0] == '\'' && val[vl - 1] == '\''))) {
                        val[vl - 1] = '\0';
                        val++;
                    }
                    int slot = -1;
                    for (int v = 0; v < nvars; v++)
                        if (strcmp(vars[v][0], ep) == 0) { slot = v; break; }
                    if (slot < 0 && nvars < 32) slot = nvars++;
                    if (slot >= 0) {
                        safe_copy(vars[slot][0], 128, ep);
                        safe_copy(vars[slot][1], 128, val);
                    }
                    continue;
                }
            }
        }

        execute_line(t, ep);
    }

    free(lines);
}

// command execution (built-ins, scripts, external commands)

static int build_argv(char *copy, char *argv[], int max) {
    int argc = 0;
    char *p = copy;
    while (*p && argc < max - 1) {
        while (*p == ' ' || *p == '\t') p++;
        if (!*p) break;
        if (*p == '"' || *p == '\'') {
            char q = *p++;
            argv[argc++] = p;
            while (*p && *p != q) p++;
            if (*p) *p++ = '\0';
        } else if (*p == '\\' && p[1]) {
            argv[argc++] = p + 1;
            p += 2;
            while (*p && *p != ' ' && *p != '\t') p++;
            if (*p) *p++ = '\0';
        } else {
            argv[argc++] = p;
            while (*p && *p != ' ' && *p != '\t') p++;
            if (*p) *p++ = '\0';
        }
    }
    argv[argc] = NULL;
    return argc;
}

// one expanded command line: built-ins, scripts, pipelines.

static void execute_line(Tab *t, char *cmdline) {
    // anchor relative paths at the tab's directory
    if (chdir(t->cwd) != 0) { /* ignore */ }

    expand_variables(cmdline, MAX_INPUT_LEN, t->last_status);
    expand_cmdsubst(cmdline, MAX_INPUT_LEN);

    int background = 0;
    size_t len = strlen(cmdline);
    while (len > 0 && (cmdline[len - 1] == ' ' || cmdline[len - 1] == '\t'))
        cmdline[--len] = '\0';
    if (len > 0 && cmdline[len - 1] == '&') {
        background = 1;
        cmdline[--len] = '\0';
        while (len > 0 && (cmdline[len - 1] == ' ' || cmdline[len - 1] == '\t'))
            cmdline[--len] = '\0';
    }
    if (!cmdline[0]) {
        if (!background) t->last_status = 0;
        return;
    }

    // multiwatch
    {
        char *p = cmdline;
        while (*p == ' ' || *p == '\t') p++;
        if (strncmp(p, "multiWatch", 10) == 0 &&
            (p[10] == ' ' || p[10] == '\t' || p[10] == '[' || p[10] == '\0')) {
            run_multiWatch(t, p);
            t->last_status = 0;
            return;
        }
    }

    if (!strchr(cmdline, '|')) {
        char copy[MAX_INPUT_LEN];
        safe_copy(copy, sizeof(copy), cmdline);
        char *argv[64];
        int argc = build_argv(copy, argv, 64);

        if (argc > 0) {
            if (strcmp(argv[0], "cd") == 0) {
                const char *dir = argv[1] ? argv[1] : get_home();
                if (chdir(dir) != 0) {
                    char err[PATH_MAX + 64];
                    snprintf(err, sizeof(err), "cd: %s: %s\n", dir, strerror(errno));
                    tab_append(t, err);
                    t->last_status = 1;
                } else {
                    if (getcwd(t->cwd, sizeof(t->cwd)) == NULL) { /* ignore */ }
                    t->last_status = 0;
                }
                return;
            }
            if (strcmp(argv[0], "exit") == 0) {
                close_current_tab();
                return;
            }
            if (strcmp(argv[0], "history") == 0) {
                sem_wait(&sh->lock);
                int start = sh->count > 1000 ? sh->count - 1000 : 0;
                for (int i = start; i < sh->count; i++) {
                    char buf[MAX_INPUT_LEN + 16];
                    snprintf(buf, sizeof(buf), "%5d  %s\n", i + 1, sh->cmds[i]);
                    tab_append(t, buf);
                }
                sem_post(&sh->lock);
                t->last_status = 0;
                return;
            }
            if (strcmp(argv[0], "jobs") == 0) {
                cleanup_jobs();
                for (int i = 0; i < tl_njobs; i++) {
                    char buf[512];
                    const char *st = tl_jobs[i].status == 1 ? "Stopped" : "Running";
                    snprintf(buf, sizeof(buf), "[%d]+  %s\t\t%s\n",
                             tl_jobs[i].job_id, st, tl_jobs[i].cmd);
                    tab_append(t, buf);
                }
                t->last_status = 0;
                return;
            }
            if (strcmp(argv[0], "fg") == 0 || strcmp(argv[0], "bg") == 0) {
                cleanup_jobs();
                int isbg = (argv[0][0] == 'b');
                int idx = -1;
                if (argv[1]) {
                    const char *a = argv[1];
                    if (*a == '%') a++;
                    if (!isdigit((unsigned char)*a)) {
                        tab_append(t, "terminator: usage: fg %<jobid>\n");
                        return;
                    }
                    int want = atoi(a);
                    for (int k = 0; k < tl_njobs; k++)
                        if (tl_jobs[k].job_id == want) { idx = k; break; }
                    if (idx < 0) {
                        char msg[64];
                        snprintf(msg, sizeof(msg),
                                 "terminator: %%%d: no such job\n", want);
                        tab_append(t, msg);
                        return;
                    }
                } else if (tl_njobs > 0) {
                    idx = tl_njobs - 1;
                } else {
                    tab_append(t, isbg ? "bg: no current job\n"
                                       : "fg: no current job\n");
                    return;
                }

                Job *j = &tl_jobs[idx];
                kill(-j->pgid, SIGCONT);
                j->status = 0;
                if (isbg) {
                    char msg[300];
                    snprintf(msg, sizeof(msg), "[%d]+ %s &\n", j->job_id, j->cmd);
                    tab_append(t, msg);
                } else {
                    tab_append(t, j->cmd);
                    tab_append(t, "\n");
                    int tty_ctrl = -1;
                    pid_t fg_saved = 0;
                    if (cmd_is_interactive(j->cmd)) {
                        tty_ctrl = open("/dev/tty", O_RDWR);
                        if (tty_ctrl >= 0) {
                            signal(SIGTTOU, SIG_IGN);
                            fg_saved = tcgetpgrp(tty_ctrl);
                            if (fg_saved < 0) fg_saved = 0;
                            tcsetpgrp(tty_ctrl, j->pgid);
                            // same note as the first start of an interactive
                            // program: tell the user where the screen went
                            char note[300];
                            snprintf(note, sizeof(note),
                                     "%s: full-screen program running on the "
                                     "terminal that started terminator - use it "
                                     "there; ctrl+z suspends it and brings the "
                                     "prompt back\n", j->cmd);
                            tab_append(t, note);
                        }
                    }
                    tl_fg_pgid = j->pgid;
                    tl_fg_running = 1;
                    int stopped = 0;
                    int st = wait_group(t, j->pgid, j->pgid, -1, &stopped);
                    tl_fg_running = 0;
                    tl_fg_pgid = 0;
                    if (tty_ctrl >= 0) {
                        tcsetpgrp(tty_ctrl, fg_saved ? fg_saved : getpgrp());
                        close(tty_ctrl);
                    }
                    if (stopped) {
                        j->status = 1;
                        char msg[300];
                        snprintf(msg, sizeof(msg), "[%d]+  Stopped\t\t%s\n",
                                 j->job_id, j->cmd);
                        tab_append(t, msg);
                    } else {
                        remove_job_at(idx);
                        t->last_status = st;
                    }
                }
                return;
            }
            if (strcmp(argv[0], "source") == 0 || strcmp(argv[0], ".") == 0) {
                if (argc < 2) {
                    tab_append(t, "source: filename argument required\n");
                    t->last_status = 2;
                    return;
                }
                run_script(t, argv[1], argv + 1, argc - 1);
                return;
            }
            // bash/sh script files are interpreted by us
            if ((strcmp(argv[0], "bash") == 0 || strcmp(argv[0], "sh") == 0) &&
                argc >= 2) {
                if (strcmp(argv[1], "-c") == 0 && argc >= 3) {
                    char cc[MAX_INPUT_LEN];
                    safe_copy(cc, sizeof(cc), argv[2]);
                    execute_line(t, cc);
                    return;
                }
                run_script(t, argv[1], argv + 1, argc - 1);
                return;
            }
            // script detection: shebang, executable text or *.sh
            {
                size_t alen = strlen(argv[0]);
                int is_sh = alen >= 3 && strcmp(argv[0] + alen - 3, ".sh") == 0;
                if (is_sh || access(argv[0], X_OK) == 0) {
                    FILE *tf = tab_fopen(t, argv[0], "r");
                    if (tf) {
                        char head[2] = {0, 0};
                        size_t rd = fread(head, 1, 2, tf);
                        fclose(tf);
                        int is_text = rd > 0 && head[0] != '\x7f';
                        if (rd >= 1 && head[0] == '#') {
                            // shebang or #-comment script
                            run_script(t, argv[0], argv, argc);
                            return;
                        }
                        if (is_text && (is_sh || access(argv[0], X_OK) == 0)) {
                            // executable text or *.sh: run it ourselves,
                            // never /bin/bash
                            run_script(t, argv[0], argv, argc);
                            return;
                        }
                    }
                }
            }
        }
    }

    run_pipeline(t, cmdline, background);
}

// adds the line to history, then runs each ';'-separated command.

static void run_command(Tab *t, char *cmdline) {
    add_to_history(cmdline);
    char *parts[16];
    int np = split_semicolons(cmdline, parts, 16);
    for (int i = 0; i < np; i++)
        execute_line(t, parts[i]);
}

// inline fallback mode: lines typed in any tab while a foreground job was
// running were queued by wait_group(); run them now, each in its own tab
static void run_queued_gui_commands(void) {
    while (gui_npend > 0) {
        int tab = gui_pend_tab[0];
        char cmd[MAX_INPUT_LEN];
        safe_copy(cmd, MAX_INPUT_LEN, gui_pend_cmd[0]);
        for (int k = 1; k < gui_npend; k++) {
            gui_pend_tab[k - 1] = gui_pend_tab[k];
            memcpy(gui_pend_cmd[k - 1], gui_pend_cmd[k], MAX_INPUT_LEN);
        }
        gui_npend--;
        if (tab >= 0 && tab < term.ntabs) {
            run_command(&term.tabs[tab], cmd);
            // the tab's waiting command has run: accept input again
            term.tabs[tab].fg_busy = 0;
        }
    }
}

// file-name auto-completion

static int cmp_match(const void *a, const void *b) {
    return strcmp((const char *)a, (const char *)b);
}

static void pick_completion(Tab *t, int idx) {
    char *m = t->cmatch[idx];
    int mlen = (int)strlen(m);
    int start = t->cword_start;
    int tail = t->input_len - t->cursor;
    int at_end = (tail == 0);
    int space = at_end ? 1 : 0;              // space only at end of line
    int newlen = start + mlen + space + tail;
    if (newlen >= MAX_INPUT_LEN - 1) { t->completing = 0; return; }

    memmove(t->input + start + mlen + space, t->input + t->cursor,
            (size_t)tail + 1);
    memcpy(t->input + start, m, (size_t)mlen);
    if (space) t->input[start + mlen] = ' ';
    t->input_len = newlen;
    t->cursor = start + mlen + space;
    t->completing = 0;
    redraw();
}

static void do_tab_completion(Tab *t) {
    if (t->completing) return;               // waiting for a digit pick
    if (t->input_len == 0) return;

    int start = t->cursor;
    while (start > 0 && t->input[start - 1] != ' ' && t->input[start - 1] != '\t')
        start--;

    char prefix[256] = {0};
    int plen = t->cursor - start;
    if (plen <= 0 || plen >= 255) return;
    memcpy(prefix, t->input + start, (size_t)plen);
    prefix[plen] = '\0';

    char (*matches)[256] = t->cmatch;
    int nmatch = 0;

    DIR *d = opendir(t->cwd);                // files of the tab's cwd
    if (!d) return;

    struct dirent *ent;
    while ((ent = readdir(d)) != NULL && nmatch < MAX_MATCHES) {
        if (strncmp(ent->d_name, prefix, (size_t)plen) == 0) {
            if (plen == 0 && (strcmp(ent->d_name, ".") == 0 ||
                              strcmp(ent->d_name, "..") == 0))
                continue;
            safe_copy(matches[nmatch], 256, ent->d_name);
            nmatch++;
        }
    }
    closedir(d);

    if (nmatch == 0) return;                 // no match: do nothing
    qsort(matches, (size_t)nmatch, 256, cmp_match);

    if (nmatch == 1) {
        const char *match = matches[0];
        int add = (int)strlen(match) - plen;

        if (t->input_len + add < MAX_INPUT_LEN - 2) {
            memmove(t->input + t->cursor + add, t->input + t->cursor,
                    (size_t)(t->input_len - t->cursor + 1));
            memcpy(t->input + t->cursor, match + plen, (size_t)add);
            t->input_len += add;
            t->cursor += add;

            // trailing space only when completing the last word, so the
            // rest of the line stays exactly as typed
            if (t->cursor == t->input_len && t->input_len < MAX_INPUT_LEN - 1) {
                t->input[t->cursor] = ' ';
                t->input[t->cursor + 1] = '\0';
                t->input_len++;
                t->cursor++;
            }
        }
        redraw();
        return;
    }

    // several matches: extend to the longest common prefix
    int lcp = plen;
    while (1) {
        char c = matches[0][lcp];
        if (c == '\0') break;
        int same = 1;
        for (int i = 1; i < nmatch; i++) {
            if (matches[i][lcp] != c) { same = 0; break; }
        }
        if (!same) break;
        lcp++;
    }

    if (lcp > plen) {
        int add = lcp - plen;
        memmove(t->input + t->cursor + add, t->input + t->cursor,
                (size_t)(t->input_len - t->cursor + 1));
        memcpy(t->input + t->cursor, matches[0] + plen, (size_t)add);
        t->input_len += add;
        t->cursor += add;
        redraw();
        return;
    }

    // still ambiguous: numbered list, user picks with a digit
    t->cword_start = start;
    t->cmatch_n = nmatch;
    t->completing = 1;

    char listbuf[2048] = {0};
    for (int i = 0; i < nmatch && i < 30; i++) {
        char tmp[80];
        snprintf(tmp, sizeof(tmp), "%2d. %-20.20s", i + 1, matches[i]);
        if (strlen(listbuf) + strlen(tmp) + 4 < sizeof(listbuf)) {
            strcat(listbuf, tmp);
            if ((i + 1) % 3 == 0) strcat(listbuf, "\n");
            else strcat(listbuf, "  ");
        }
    }
    if (listbuf[0] && listbuf[strlen(listbuf) - 1] != '\n')
        strcat(listbuf, "\n");
    tab_append(t, listbuf);
    redraw();
}

// copy / paste via x11 selections

static void input_insert(Tab *t, const char *s, int n) {
    if (n <= 0) return;
    if (t->input_len + n >= MAX_INPUT_LEN)
        n = MAX_INPUT_LEN - 1 - t->input_len;
    if (n <= 0) return;
    memmove(t->input + t->cursor + n, t->input + t->cursor,
            (size_t)(t->input_len - t->cursor + 1));
    memcpy(t->input + t->cursor, s, (size_t)n);
    t->input_len += n;
    t->cursor += n;
}

static void paste_text(Tab *t, const char *s, size_t n) {
    if (t->searching) {
        size_t sl = strlen(t->search_term);
        if (sl + n < sizeof(t->search_term)) {
            memcpy(t->search_term + sl, s, n);
            t->search_term[sl + n] = '\0';
        }
    } else {
        input_insert(t, s, (int)n);
    }
    redraw();
}

static void set_clipboard(const char *s) {
    safe_copy(clip, sizeof(clip), s);
    if (!term.dpy) return;
    XStoreBytes(term.dpy, clip, (int)strlen(clip));
    XSetSelectionOwner(term.dpy, XA_PRIMARY, term.win, CurrentTime);
    if (clip_atom != None)
        XSetSelectionOwner(term.dpy, clip_atom, term.win, CurrentTime);
    XFlush(term.dpy);
}

static void request_paste(Tab *t) {
    if (!term.dpy) return;
    Atom sel = XA_PRIMARY;
    Window owner = None;
    if (clip_atom != None) {
        owner = XGetSelectionOwner(term.dpy, clip_atom);
        if (owner != None) sel = clip_atom;
    }
    if (owner == None) {
        owner = XGetSelectionOwner(term.dpy, XA_PRIMARY);
        if (owner != None) sel = XA_PRIMARY;
    }
    if (owner == term.win) {                 // we own it: use our copy
        paste_text(t, clip, strlen(clip));
        return;
    }
    if (owner == None) {                     // fall back to the cut buffer
        int n = 0;
        char *d = XFetchBytes(term.dpy, &n);
        if (d) {
            paste_text(t, d, (size_t)(n > 0 ? n : 0));
            XFree(d);
        }
        return;
    }
    if (sel_prop_atom != None) {
        XConvertSelection(term.dpy, sel, XA_STRING, sel_prop_atom,
                          term.win, CurrentTime);
        paste_pending = 1;
    }
}

// ctrl+r history search

// longest common substring length of a and b (rolling dp)

static int lcs_len(const char *a, const char *b) {
    int n = (int)strlen(a);
    if (n > 256) n = 256;
    int m = (int)strnlen(b, 512);
    if (n == 0 || m == 0) return 0;
    static int dp[2][257];
    memset(dp[0], 0, sizeof(dp[0]));
    int best = 0;
    for (int i = 1; i <= n; i++) {
        int r = i & 1, p = r ^ 1;
        dp[r][0] = 0;
        for (int j = 1; j <= m; j++) {
            if (a[i - 1] == b[j - 1]) {
                dp[r][j] = dp[p][j - 1] + 1;
                if (dp[r][j] > best) best = dp[r][j];
            } else {
                dp[r][j] = 0;
            }
        }
    }
    return best;
}

static void do_hist_search(Tab *t) {
    char term_str[256];
    safe_copy(term_str, sizeof(term_str), t->search_term);

    char echo[300];
    snprintf(echo, sizeof(echo), "Enter search term: %s\n", term_str);
    tab_append(t, echo);
    t->searching = 0;
    t->search_term[0] = '\0';

    int tl = (int)strlen(term_str);
    int found = 0;

    sem_wait(&sh->lock);
    if (tl > 0) {
        // (a) most recent exact match
        for (int i = sh->count - 1; i >= 0; i--) {
            if (strcmp(sh->cmds[i], term_str) == 0) {
                tab_append(t, sh->cmds[i]);
                tab_append(t, "\n");
                found = 1;
                break;
            }
        }
        // (b) commands sharing the longest common substring (> 2 chars)
        if (!found && tl > 2) {
            int best = 0;
            for (int i = sh->count - 1; i >= 0; i--) {
                if (strstr(sh->cmds[i], term_str)) { best = tl; break; }
            }
            int start = sh->count > 1000 ? sh->count - 1000 : 0;
            int cnt = sh->count - start;
            int *cache = malloc((size_t)(cnt > 0 ? cnt : 1) * sizeof(int));
            if (cache) {
                for (int k = 0; k < cnt; k++) {
                    cache[k] = lcs_len(term_str, sh->cmds[start + k]);
                    if (cache[k] > best) best = cache[k];
                }
                if (best > 2) {
                    int shown = 0;
                    for (int k = cnt - 1; k >= 0 && shown < 50; k--) {
                        if (cache[k] == best) {
                            tab_append(t, sh->cmds[start + k]);
                            tab_append(t, "\n");
                            shown++;
                        }
                    }
                    found = shown > 0;
                }
                free(cache);
            }
        }
    }
    sem_post(&sh->lock);

    if (!found)
        tab_append(t, "No match for search term in history\n");
    t->last_status = found ? 0 : 1;
}

// rebindable hotkeys

static const struct { const char *name; int action; } action_table[] = {
    { "move-left",         A_LEFT     },
    { "move-right",        A_RIGHT    },
    { "move-home",         A_HOME     },
    { "move-end",          A_END      },
    { "history-prev",      A_HISTUP   },
    { "history-next",      A_HISTDN   },
    { "delete-to-start",   A_DELSTART },
    { "delete-to-end",     A_DELEND   },
    { "delete-prev-word",  A_DELWORD  },
    { "clear-screen",      A_CLEAR    },
    { "eof",               A_EOFDEL   },
    { "copy",              A_COPY     },
    { "paste",             A_PASTE    },
    { "history-search",    A_SEARCH   },
    { "new-tab",           A_NEWTAB   },
    { "close-tab",         A_CLOSETAB },
    { "next-tab",          A_NEXTTAB  },
    { "complete",          A_COMPLETE },
    { "interrupt",         A_INTR     },
    { "suspend",           A_SUSP     },
    { NULL, 0 }
};

static int action_by_name(const char *name) {
    for (int i = 0; action_table[i].name; i++)
        if (strcmp(action_table[i].name, name) == 0)
            return action_table[i].action;
    return A_NONE;
}

static const char *action_name(int action) {
    for (int i = 0; action_table[i].name; i++)
        if (action_table[i].action == action)
            return action_table[i].name;
    return "?";
}

static void rc_warnf(const char *fmt, ...) {
    va_list ap;
    size_t len = strlen(rc_warn);
    if (len >= sizeof(rc_warn) - 128) return;
    va_start(ap, fmt);
    vsnprintf(rc_warn + len, sizeof(rc_warn) - len - 1, fmt, ap);
    va_end(ap);
    strcat(rc_warn, "\n");
}

static void bind_key(int mods, KeySym ks, int action, int custom,
                     int lineno) {
    for (int i = 0; i < nbindings; i++) {
        if (bindings[i].ks == ks && bindings[i].mods == mods) {
            if (custom && bindings[i].custom) {
                rc_warnf("terminator: ~/.terminatorrc: line %d: conflict: "
                         "%s already bound to '%s' - keeping that binding",
                         lineno, action_name(action),
                         action_name(bindings[i].action));
                return;
            }
            if (custom) {                    // override a default binding
                bindings[i].action = action;
                bindings[i].custom = 1;
                return;
            }
            return;                          // duplicate default
        }
    }
    if (nbindings >= 64) return;
    bindings[nbindings].mods = mods;
    bindings[nbindings].ks = ks;
    bindings[nbindings].action = action;
    bindings[nbindings].custom = custom;
    nbindings++;
}

static void load_bindings(void) {
    nbindings = 0;
    // defaults
    bind_key(0,        XK_Left,  A_LEFT,     0, 0);
    bind_key(0,        XK_Right, A_RIGHT,    0, 0);
    bind_key(0,        XK_Up,    A_HISTUP,   0, 0);
    bind_key(0,        XK_Down,  A_HISTDN,   0, 0);
    bind_key(MOD_CTRL, XK_a,     A_HOME,     0, 0);
    bind_key(MOD_CTRL, XK_e,     A_END,      0, 0);
    bind_key(MOD_CTRL, XK_u,     A_DELSTART, 0, 0);
    bind_key(MOD_CTRL, XK_k,     A_DELEND,   0, 0);
    bind_key(MOD_CTRL, XK_w,     A_DELWORD,  0, 0);
    bind_key(MOD_CTRL, XK_l,     A_CLEAR,    0, 0);
    bind_key(MOD_CTRL, XK_d,     A_EOFDEL,   0, 0);
    bind_key(MOD_CTRL | MOD_SHIFT, XK_c, A_COPY,  0, 0);
    bind_key(MOD_CTRL | MOD_SHIFT, XK_v, A_PASTE, 0, 0);
    bind_key(MOD_CTRL, XK_r,     A_SEARCH,   0, 0);
    bind_key(MOD_CTRL, XK_t,     A_NEWTAB,   0, 0);
    bind_key(MOD_CTRL, XK_s,     A_NEXTTAB,  0, 0);
    bind_key(MOD_CTRL | MOD_SHIFT, XK_w, A_CLOSETAB, 0, 0);
    bind_key(0,        XK_Tab,   A_COMPLETE, 0, 0);
    bind_key(MOD_CTRL, XK_space, A_COMPLETE, 0, 0);
    bind_key(MOD_CTRL, XK_c,     A_INTR,     0, 0);
    bind_key(MOD_CTRL, XK_z,     A_SUSP,     0, 0);

    // user overrides: ~/.terminatorrc, one "bind <key> <action>" per line
    char path[PATH_MAX];
    snprintf(path, sizeof(path), "%s/.terminatorrc", get_home());
    FILE *f = fopen(path, "r");
    if (!f) return;

    char line[512];
    int lineno = 0;
    while (fgets(line, sizeof(line), f)) {
        lineno++;
        size_t l = strlen(line);
        if (l && line[l - 1] == '\n') line[l - 1] = '\0';
        char *p = line;
        while (*p == ' ' || *p == '\t') p++;
        if (*p == '#' || *p == '\0') continue;

        char a[64], combo[128], act[64];
        if (sscanf(p, "%63s %127s %63s", a, combo, act) != 3 ||
            strcmp(a, "bind") != 0) {
            rc_warnf("terminator: ~/.terminatorrc: line %d: invalid line "
                     "(expected 'bind <key> <action>') - default kept",
                     lineno);
            continue;
        }

        int mods = 0;
        char keyname[64] = "";
        char tmp[128];
        safe_copy(tmp, sizeof(tmp), combo);
        char *save = NULL;
        char *tok = strtok_r(tmp, "+", &save);
        int ntok = 0;
        while (tok) {
            char *next = strtok_r(NULL, "+", &save);
            if (!next) {                          // last part = key name
                safe_copy(keyname, sizeof(keyname), tok);
            } else if (strcmp(tok, "ctrl") == 0 || strcmp(tok, "control") == 0) {
                mods |= MOD_CTRL;
            } else if (strcmp(tok, "shift") == 0) {
                mods |= MOD_SHIFT;
            } else if (strcmp(tok, "alt") == 0 || strcmp(tok, "meta") == 0) {
                mods |= MOD_ALT;
            } else {
                rc_warnf("terminator: ~/.terminatorrc: line %d: unknown "
                         "modifier '%s' - default kept", lineno, tok);
                mods = -1;
                break;
            }
            tok = next;
            ntok++;
        }
        if (mods < 0 || !keyname[0]) continue;

        KeySym ks = XStringToKeysym(keyname);
        if (!ks) {
            rc_warnf("terminator: ~/.terminatorrc: line %d: unknown key "
                     "'%s' - default kept", lineno, keyname);
            continue;
        }
        if (ks >= XK_A && ks <= XK_Z) {           // normalize letter case
            ks += XK_a - XK_A;
            mods |= MOD_SHIFT;
        }

        int action = action_by_name(act);
        if (action == A_NONE) {
            rc_warnf("terminator: ~/.terminatorrc: line %d: unknown action "
                     "'%s' - default kept", lineno, act);
            continue;
        }
        bind_key(mods, ks, action, 1, lineno);
    }
    fclose(f);
}

static int lookup_binding(int mods, KeySym ks) {
    for (int i = 0; i < nbindings; i++)
        if (bindings[i].ks == ks && bindings[i].mods == mods)
            return bindings[i].action;
    return A_NONE;
}

// key dispatch

static void dispatch_action(Tab *t, int action) {
        // a foreground command is running in this tab: keys that would edit the
        // input line are ignored; tab switching, ctrl+r, copy, clear and
        // ctrl+c/ctrl+z keep working
    if (t->fg_busy) {
        switch (action) {
        case A_HISTUP: case A_HISTDN:
        case A_DELSTART: case A_DELEND: case A_DELWORD:
        case A_EOFDEL: case A_COMPLETE: case A_PASTE:
            return;
        }
    }
    switch (action) {
    case A_LEFT:
        if (t->cursor > 0) t->cursor--;
        break;
    case A_RIGHT:
        if (t->cursor < t->input_len) t->cursor++;
        break;
    case A_HOME:
        t->cursor = 0;
        break;
    case A_END:
        t->cursor = t->input_len;
        break;
    case A_HISTUP:
        if (sh->count > 0) {
            if (t->hist_idx < 0) t->hist_idx = sh->count;
            if (t->hist_idx > 0) t->hist_idx--;
            hist_copy(t->hist_idx, t->input, MAX_INPUT_LEN);
            t->input_len = (int)strlen(t->input);
            t->cursor = t->input_len;
        }
        break;
    case A_HISTDN:
        if (t->hist_idx >= 0 && t->hist_idx < sh->count - 1) {
            t->hist_idx++;
            hist_copy(t->hist_idx, t->input, MAX_INPUT_LEN);
            t->input_len = (int)strlen(t->input);
            t->cursor = t->input_len;
        } else {
            t->hist_idx = -1;
            t->input[0] = 0;
            t->input_len = t->cursor = 0;
        }
        break;
    case A_DELSTART:
        memmove(t->input, t->input + t->cursor,
                (size_t)(t->input_len - t->cursor + 1));
        t->input_len -= t->cursor;
        t->cursor = 0;
        break;
    case A_DELEND:
        t->input[t->cursor] = 0;
        t->input_len = t->cursor;
        break;
    case A_DELWORD: {
        int c = t->cursor;
        while (c > 0 && (t->input[c - 1] == ' ' || t->input[c - 1] == '\t')) c--;
        while (c > 0 && t->input[c - 1] != ' ' && t->input[c - 1] != '\t') c--;
        memmove(t->input + c, t->input + t->cursor,
                (size_t)(t->input_len - t->cursor + 1));
        t->input_len -= (t->cursor - c);
        t->cursor = c;
        break;
    }
    case A_CLEAR:
        t->nlines = 0;
        t->partial = 0;
        break;
    case A_EOFDEL:
        if (t->input_len == 0) {            // empty line: close the tab
            close_current_tab();
            return;
        }
        if (t->cursor < t->input_len) {     // delete char under cursor
            memmove(t->input + t->cursor, t->input + t->cursor + 1,
                    (size_t)(t->input_len - t->cursor));
            t->input_len--;
        }
        break;
    case A_COPY:
        set_clipboard(t->input);
        break;
    case A_PASTE:
        request_paste(t);
        return;
    case A_SEARCH:
        t->searching = 1;
        t->search_term[0] = 0;
        break;
    case A_NEWTAB:
        new_tab();
        return;
    case A_CLOSETAB:
        close_current_tab();
        return;
    case A_NEXTTAB:
        if (term.ntabs > 1) {
            term.active = (term.active + 1) % term.ntabs;
        }
        break;
    case A_COMPLETE:
        do_tab_completion(t);
        return;
    case A_INTR:
        if (tab_in_fd[term.active] >= 0)      // thread and process mode alike
            send_frame(tab_in_fd[term.active], 'I', "", 0);
        else if (mw_active)
            mw_active = 0;
        t->input_len = t->cursor = 0;
        t->input[0] = 0;
        t->multiline = 0;
        t->pending[0] = 0;
        t->pend_sep[0] = 0;
        t->completing = 0;
        if (tab_in_fd[term.active] < 0)       // inline mode: no backend to tell
            tab_append(t, "^C\n");
        break;
    case A_SUSP:
        if (tab_in_fd[term.active] >= 0)
            send_frame(tab_in_fd[term.active], 'Z', "", 0);
        break;
    default:
        return;
    }
    redraw();
}

// key handling

static void handle_key(XKeyEvent *ev) {
    Tab *t = &term.tabs[term.active];
    char buf[32];
    KeySym ks_raw, ks;
    int len = XLookupString(ev, buf, sizeof(buf), &ks_raw, NULL);
    ks = ks_raw;
    if (ks >= XK_A && ks <= XK_Z) ks += XK_a - XK_A;

    int mods = 0;
    if (ev->state & ControlMask) mods |= MOD_CTRL;
    if (ev->state & ShiftMask)   mods |= MOD_SHIFT;
    if (ev->state & Mod1Mask)    mods |= MOD_ALT;

    // ctrl+r search mode
    if (t->searching) {
        if (ks == XK_Return || ks == XK_KP_Enter) {
            do_hist_search(t);
            redraw();
            return;
        }
        if (ks == XK_Escape) {
            t->searching = 0;
            t->search_term[0] = 0;
            redraw();
            return;
        }
        if (ks == XK_BackSpace || ks == XK_Delete) {
            size_t sl = strlen(t->search_term);
            if (sl > 0) t->search_term[sl - 1] = 0;
            redraw();
            return;
        }
        if (len == 1 && isprint((unsigned char)buf[0])) {
            size_t sl = strlen(t->search_term);
            if (sl < sizeof(t->search_term) - 1) {
                t->search_term[sl] = buf[0];
                t->search_term[sl + 1] = 0;
            }
            redraw();
        }
        return;
    }

    // numbered completion pick
    if (t->completing) {
        if (len == 1 && buf[0] >= '1' && buf[0] <= '9' &&
            buf[0] - '1' < t->cmatch_n) {
            pick_completion(t, buf[0] - '1');
            return;
        }
        t->completing = 0;                    // any other key cancels
    }

    // rebindable actions
    int action = lookup_binding(mods, ks);
    if (action != A_NONE) {
        dispatch_action(t, action);
        return;
    }

        // a foreground command is running in this tab: the prompt takes no
        // input until it ends; the bound keys above (tab switching, ctrl+r,
        // ctrl+c/ctrl+z, ...) still answer
    if (t->fg_busy) return;

    if (ks == XK_Return || ks == XK_KP_Enter) {
        char prompt[PROMPT_MAX];
        tab_prompt(t, prompt, sizeof(prompt));
        char echo[MAX_INPUT_LEN + PROMPT_MAX];
        if (t->multiline)
            snprintf(echo, sizeof(echo), "> %s\n", t->input);
        else
            snprintf(echo, sizeof(echo), "%s%s\n", prompt, t->input);
        tab_append(t, echo);

        int nbs = 0;
        for (int i = t->input_len - 1; i >= 0 && t->input[i] == '\\'; i--)
            nbs++;

        char chunk[MAX_INPUT_LEN];
        safe_copy(chunk, sizeof(chunk), t->input);
        if (nbs % 2 == 1)                     // drop one trailing backslash
            chunk[strlen(chunk) - 1] = '\0';

                // completeness is judged on the joined line: a quote opened in an
                // earlier chunk may be closed in this one
        char full[MAX_INPUT_LEN * 2];
        if (t->multiline)
            snprintf(full, sizeof(full), "%s%s%s",
                     t->pending, t->pend_sep, chunk);
        else
            snprintf(full, sizeof(full), "%s", chunk);

        int ended_quote = 0;
        int incomplete = (nbs % 2 == 1) ? 1 : line_incomplete(full, &ended_quote);

        // a line ending with '|' also continues on the next line (bash)
        if (!incomplete) {
            const char *tail = full + strlen(full);
            while (tail > full && (tail[-1] == ' ' || tail[-1] == '\t')) tail--;
            if (tail > full && tail[-1] == '|') incomplete = 1;
        }

        if (incomplete) {                     // keep reading: "> " prompt
            line_incomplete(full, &ended_quote);
            const char *sep = ended_quote ? "\n"
                              : (nbs % 2 == 1 ? "" : "\n");
            safe_copy(t->pending, sizeof(t->pending), full);
            t->pend_sep[0] = sep[0];
            t->pend_sep[1] = 0;
            t->multiline = 1;
            t->input_len = t->cursor = 0;
            t->input[0] = 0;
            redraw();
            return;
        }

        t->multiline = 0;
        t->pending[0] = 0;
        t->pend_sep[0] = 0;
        t->input_len = t->cursor = 0;
        t->input[0] = 0;
        t->hist_idx = -1;
        t->completing = 0;

        if (full[0]) {
            if (tab_in_fd[term.active] >= 0) {    // hand the line to the tab
                send_frame(tab_in_fd[term.active], 'L', full, strlen(full));
                t->fg_busy = 1;               // cleared by the tab's 'x'
            } else {
                run_command(t, full);
                run_queued_gui_commands();    // lines typed while it ran
            }
        }
        redraw();
        return;
    }

    if (ks == XK_BackSpace || ks == XK_Delete) {
        if (t->cursor > 0) {
            memmove(t->input + t->cursor - 1, t->input + t->cursor,
                    (size_t)(t->input_len - t->cursor + 1));
            t->input_len--;
            t->cursor--;
            redraw();
        }
        return;
    }

    if (len == 1 && isprint((unsigned char)buf[0]) &&
        t->input_len < MAX_INPUT_LEN - 1) {
        input_insert(t, buf, 1);
        redraw();
    }
}

// tab lifecycle

// thread mode: one pthread per tab runs the same backend loop a
// process-mode tab runs; only the thread-local state differs

typedef struct {
    Tab *t;
    int  in_fd, out_fd;
} TabThrArg;

static void *tab_thread_entry(void *arg) {
    TabThrArg *a = arg;
    am_tab_thread = 1;
    Tab *t = a->t;
    int in_fd = a->in_fd, out_fd = a->out_fd;
    free(a);
    tab_child_main(t, in_fd, out_fd);
    return NULL;
}

static void tab_thread_start(Tab *t, int in_fd, int out_fd) {
    TabThrArg *a = malloc(sizeof(*a));
    if (!a) return;
    a->t = t;
    a->in_fd = in_fd;
    a->out_fd = out_fd;
    pthread_t tid;
    if (pthread_create(&tid, NULL, tab_thread_entry, a) != 0) {
        free(a);
        return;
    }
    pthread_detach(tid);
}

// removes tab slot i (gui side). a process-mode tab child is killed; a
// thread-mode tab backend exits when its command pipe hits eof.

static void remove_tab_at(int i) {
    if (term.process_mode && tab_pid[i] > 0) {
        kill(tab_pid[i], SIGKILL);
        waitpid(tab_pid[i], NULL, 0);
        if (tab_out_fd[i] >= 0) close(tab_out_fd[i]);
        if (tab_in_fd[i] >= 0) close(tab_in_fd[i]);
    } else if (tab_out_fd[i] >= 0) {          // thread mode: stop the backend
        close(tab_in_fd[i]);                  // eof makes the thread exit
        close(tab_out_fd[i]);
    }
    tab_pid[i] = -1;
    tab_out_fd[i] = tab_in_fd[i] = -1;

    for (int k = i; k < term.ntabs - 1; k++) {
        term.tabs[k] = term.tabs[k + 1];
        tab_pid[k] = tab_pid[k + 1];
        tab_out_fd[k] = tab_out_fd[k + 1];
        tab_in_fd[k] = tab_in_fd[k + 1];
    }
    term.ntabs--;
    if (term.active >= term.ntabs) term.active = term.ntabs - 1;
    if (term.active < 0) term.active = 0;

    if (term.ntabs == 0) {                    // last tab closed: exit
        save_history();
        if (term.dpy) XCloseDisplay(term.dpy);
        exit(0);
    }
    redraw();
}

static void close_current_tab(void) {
    if (am_tab_child)
        tab_backend_exit();                   // 'exit' inside a tab backend
    remove_tab_at(term.active);
}

static void new_tab(void) {
    if (term.ntabs >= MAX_TABS) return;
    int i = term.ntabs;

    if (!term.process_mode) {
        // thread mode: each tab is a pthread of this same process, talking
        // to the gui over the same framed pipes a process-mode tab uses
        int pin[2], pout[2];
        if (pipe(pin) < 0 || pipe(pout) < 0) return;

        Tab *t = &term.tabs[i];
        memset(t, 0, sizeof(*t));
        t->out_fd = -1;
        if (getcwd(t->cwd, sizeof(t->cwd)) == NULL) {
            t->cwd[0] = '/';
            t->cwd[1] = '\0';
        }
        t->hist_idx = -1;
        tab_out_fd[i] = pout[0];
        tab_in_fd[i] = pin[1];
        term.active = i;
        term.ntabs++;
        // the backend's pipe ends stay open here: the pthread shares this
        // fd table, closing them would cut its own connection off
        tab_thread_start(t, pin[0], pout[1]);
        redraw();
        return;
    }

        // process mode: each tab is its own forked process talking to the gui
        // through two pipes; a crashed tab cannot take the others down
    int pin[2], pout[2];
    if (pipe(pin) < 0 || pipe(pout) < 0) return;
    pid_t pid = fork();
    if (pid < 0) {
        close(pin[0]); close(pin[1]);
        close(pout[0]); close(pout[1]);
        return;
    }
    if (pid == 0) {
        close(pin[1]);
        close(pout[0]);
        tab_child_main(&term.tabs[0], pin[0], pout[1]);
        _exit(0);
    }
    close(pin[0]);
    close(pout[1]);

    Tab *t = &term.tabs[i];
    memset(t, 0, sizeof(*t));
    t->out_fd = -1;
    if (getcwd(t->cwd, sizeof(t->cwd)) == NULL) {
        t->cwd[0] = '/';
        t->cwd[1] = '\0';
    }
    t->hist_idx = -1;
    tab_pid[i] = pid;
    tab_out_fd[i] = pout[0];
    tab_in_fd[i] = pin[1];
    term.active = i;
    term.ntabs++;
    redraw();
}

// gui side: read framed messages coming from a tab process.

static void parent_pump(int i) {
    Tab *t = &term.tabs[i];
    char tmp[8192];
    ssize_t n = read(tab_out_fd[i], tmp, sizeof(tmp));
    if (n <= 0) {                             // eof: tab closed or crashed
        remove_tab_at(i);
        return;
    }
    if (t->net_len + n > (int)sizeof(t->net_buf)) t->net_len = 0;
    memcpy(t->net_buf + t->net_len, tmp, (size_t)n);
    t->net_len += (int)n;

    static char pl[65536];
    int off = 0;
    while (t->net_len - off >= FRAME_HDR) {
        char type = t->net_buf[off];
        uint32_t flen;
        memcpy(&flen, t->net_buf + off + 1, 4);
        if (flen > sizeof(t->net_buf)) {      // corrupt: resynchronise
            t->net_len = 0;
            return;
        }
        if (t->net_len - off < (int)(FRAME_HDR + flen)) break;
        if (flen < sizeof(pl)) {
            memcpy(pl, t->net_buf + off + FRAME_HDR, flen);
            pl[flen] = '\0';
            if (type == 'O') tab_append(t, pl);
            else if (type == 'C') safe_copy(t->cwd, sizeof(t->cwd), pl);
            else if (type == 'X') t->fg_busy = 0;   // command finished
        }
        off += (int)(FRAME_HDR + flen);
    }
    memmove(t->net_buf, t->net_buf + off, (size_t)(t->net_len - off));
    t->net_len -= off;
    redraw();
}

// gui side: drain a background job's captured output into the active tab.

static void drain_job(int j) {
    char buf[4096];
    ssize_t n = read(tl_jobs[j].cap_fd, buf, sizeof(buf) - 1);
    if (n > 0) {
        buf[n] = '\0';
        tab_append(&term.tabs[term.active], buf);
        redraw();
    } else {
        close(tl_jobs[j].cap_fd);
        tl_jobs[j].cap_fd = -1;
    }
}

// process mode: the tab child (no x11 here)

static void tab_child_main(Tab *t, int in_fd, int out_fd) {
    am_tab_child = 1;
    my_in_fd = in_fd;
    {
        // this tab process needs its own sigchld self-pipe: the pipe made
        // in main() is inherited by everyone, so a wakeup for this tab
        // could be drained by the gui or a sibling first - then this
        // wait_group() would never wake (no 'x' frame, input blocked
        // forever). a private pipe makes the wakeup exclusive
        int pfd[2];
        if (pipe(pfd) == 0) {
            sigchld_rfd = pfd[0];
            sigchld_wfd = pfd[1];
            fcntl(sigchld_rfd, F_SETFL, O_NONBLOCK);
            struct sigaction sa;
            memset(&sa, 0, sizeof(sa));
            sa.sa_handler = sigchld_handler;
            sigemptyset(&sa.sa_mask);
            sa.sa_flags = SA_RESTART;     // same as setup_signals()
            sigaction(SIGCHLD, &sa, NULL);
        }
    }
    if (!am_tab_thread) {
        // a tab process owns its private copy of everything: re-initialise
        memset(t, 0, sizeof(*t));
        t->hist_idx = -1;
        if (getcwd(t->cwd, sizeof(t->cwd)) == NULL) {
            t->cwd[0] = '/';
            t->cwd[1] = '\0';
        }
        term.ntabs = 1;
        term.active = 0;
    }
    t->out_fd = out_fd;   // thread mode: the gui already filled the struct in
    my_out_fd = out_fd;   // kept thread-local: survives tab-array shifts

    for (;;) {
        // run commands that were typed while a foreground job was running
        while (child_npend > 0) {
            char cmd[MAX_INPUT_LEN];
            safe_copy(cmd, MAX_INPUT_LEN, child_pend[0]);
            for (int k = 1; k < child_npend; k++)
                memcpy(child_pend[k - 1], child_pend[k], MAX_INPUT_LEN);
            child_npend--;
            run_command(t, cmd);
            send_frame(my_out_fd, 'C', t->cwd, strlen(t->cwd));
            send_frame(my_out_fd, 'X', "", 0);
        }

        // background jobs of this tab live in this process; while the tab
        // is idle, watch their capture pipes and the sigchld self-pipe -
        // without this, their output is never read and they are never
        // reaped. blocking select() - no busy wait
        for (;;) {
            fd_set rf;
            FD_ZERO(&rf);
            FD_SET(my_in_fd, &rf);
            int maxfd = my_in_fd;
            if (sigchld_rfd >= 0) {
                FD_SET(sigchld_rfd, &rf);
                if (sigchld_rfd > maxfd) maxfd = sigchld_rfd;
            }
            for (int j = 0; j < tl_njobs; j++) {
                if (tl_jobs[j].cap_fd >= 0) {
                    FD_SET(tl_jobs[j].cap_fd, &rf);
                    if (tl_jobs[j].cap_fd > maxfd)
                        maxfd = tl_jobs[j].cap_fd;
                }
            }
            struct timeval tv = {0, 100000};
            int rv = select(maxfd + 1, &rf, NULL, NULL, &tv);
            if (rv < 0) {
                if (errno == EINTR) continue;
                break;
            }
            if (rv == 0) continue;    // idle tick: re-check background jobs
            int gui_only = 1;
            for (int j = 0; j < tl_njobs; j++) {
                int fd = tl_jobs[j].cap_fd;
                if (fd >= 0 && FD_ISSET(fd, &rf)) {
                    char buf[4096];
                    ssize_t n = read(fd, buf, sizeof(buf) - 1);
                    if (n > 0) {
                        buf[n] = '\0';
                        tab_append(t, buf);
                        redraw();
                    } else if (n == 0 ||
                               (errno != EINTR && errno != EAGAIN)) {
                        close(fd);
                        tl_jobs[j].cap_fd = -1;
                        cleanup_jobs();   // writers gone: reap the group
                    }
                    gui_only = 0;
                }
            }
            if (sigchld_rfd >= 0 && FD_ISSET(sigchld_rfd, &rf)) {
                char db[64];
                while (read(sigchld_rfd, db, sizeof(db)) > 0) {}
                cleanup_jobs();
                gui_only = 0;
            }
            if (gui_only) break;          // only the gui answered: read it
        }

        char type;
        char pl[MAX_INPUT_LEN + 16];
        size_t plen;
        int r = read_frame(my_in_fd, &type, pl, sizeof(pl) - 1, &plen);
        if (r <= 0) tab_backend_exit();       // gui closed the tab

        if (type == 'L') {
            run_command(t, pl);
            send_frame(my_out_fd, 'C', t->cwd, strlen(t->cwd));
            send_frame(my_out_fd, 'X', "", 0);
        } else if (type == 'I') {
            if (tl_fg_running) {
                kill(-tl_fg_pgid, SIGINT);
                tab_append(t, "^C\n");
            }
        } else if (type == 'Z') {
            if (tl_fg_running)
                kill(-tl_fg_pgid, SIGTSTP);
        } else if (type == 'Q') {
            tab_backend_exit();
        }
    }
}

// main

int main(int argc, char *argv[]) {
    term.process_mode = 0;
    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "useProcess=True") == 0)
            term.process_mode = 1;
    }

    setup_signals();
    history_init();
    load_history();

    for (int i = 0; i < MAX_TABS; i++) {
        tab_pid[i] = -1;
        tab_out_fd[i] = tab_in_fd[i] = -1;
    }

    term.dpy = XOpenDisplay(NULL);
    if (!term.dpy) die("cannot open display");
    term.screen = DefaultScreen(term.dpy);
    term.width = 900;
    term.height = 550;

    term.win = XCreateSimpleWindow(term.dpy, RootWindow(term.dpy, term.screen),
                                   80, 80, term.width, term.height, 1,
                                   BlackPixel(term.dpy, term.screen),
                                   WhitePixel(term.dpy, term.screen));
    XStoreName(term.dpy, term.win, "Terminator");
    XSelectInput(term.dpy, term.win,
                 ExposureMask | KeyPressMask | StructureNotifyMask |
                 ButtonPressMask | Button4Mask | Button5Mask |
                 PropertyChangeMask);
    term.wm_delete = XInternAtom(term.dpy, "WM_DELETE_WINDOW", False);
    XSetWMProtocols(term.dpy, term.win, &term.wm_delete, 1);
    term.gc = XCreateGC(term.dpy, term.win, 0, NULL);
    term.font = XLoadQueryFont(term.dpy, FONT_NAME);
    if (term.font) XSetFont(term.dpy, term.gc, term.font->fid);
    sel_prop_atom = XInternAtom(term.dpy, "TERMINATOR_SEL", False);
    clip_atom = XInternAtom(term.dpy, "CLIPBOARD", False);

    load_bindings();                          // ~/.terminatorrc overrides

    XMapWindow(term.dpy, term.win);

    term.ntabs = 0;
    new_tab();

    if (rc_warn[0]) {
        tab_append(&term.tabs[0], rc_warn);
        redraw();
    }

    if (term.process_mode)
        tab_append(&term.tabs[0], "running in process mode\n");
    else
        tab_append(&term.tabs[0], "running in thread mode\n");
    redraw();

    int xfd = ConnectionNumber(term.dpy);
    while (1) {
        fd_set rf;
        FD_ZERO(&rf);
        FD_SET(xfd, &rf);
        FD_SET(sigchld_rfd, &rf);
        int maxfd = xfd > sigchld_rfd ? xfd : sigchld_rfd;

        for (int i = 0; i < term.ntabs; i++) {
            if (tab_out_fd[i] >= 0) {
                FD_SET(tab_out_fd[i], &rf);
                if (tab_out_fd[i] > maxfd) maxfd = tab_out_fd[i];
            }
        }
        for (int j = 0; j < tl_njobs; j++) {
            if (tl_jobs[j].cap_fd >= 0) {
                FD_SET(tl_jobs[j].cap_fd, &rf);
                if (tl_jobs[j].cap_fd > maxfd) maxfd = tl_jobs[j].cap_fd;
            }
        }

        struct timeval tv = {0, 100000};
        if (select(maxfd + 1, &rf, NULL, NULL, &tv) > 0) {
            if (FD_ISSET(sigchld_rfd, &rf)) {
                char db[64];
                while (read(sigchld_rfd, db, sizeof(db)) > 0) {}
                cleanup_jobs();
            }
            // reverse order: pumping may close a tab and shift the array
            for (int i = term.ntabs - 1; i >= 0; i--) {
                if (tab_out_fd[i] >= 0 && FD_ISSET(tab_out_fd[i], &rf))
                    parent_pump(i);
            }
            for (int j = 0; j < tl_njobs; j++) {
                if (tl_jobs[j].cap_fd >= 0 && FD_ISSET(tl_jobs[j].cap_fd, &rf))
                    drain_job(j);
            }
            if (FD_ISSET(xfd, &rf)) {
                while (XPending(term.dpy)) {
                    XEvent ev;
                    XNextEvent(term.dpy, &ev);
                    switch (ev.type) {
                    case Expose:
                        if (ev.xexpose.count == 0) redraw();
                        break;
                    case KeyPress:
                        handle_key(&ev.xkey);
                        break;
                    case ConfigureNotify:
                        term.width  = ev.xconfigure.width;
                        term.height = ev.xconfigure.height;
                        redraw();
                        break;
                    case ButtonPress:
                        if (ev.xbutton.button == 4) {
                            Tab *t = &term.tabs[term.active];
                            t->scroll++;
                            redraw();
                        } else if (ev.xbutton.button == 5) {
                            Tab *t = &term.tabs[term.active];
                            if (t->scroll > 0) t->scroll--;
                            redraw();
                        } else if (ev.xbutton.y < TAB_BAR_H) {
                            int idx = (ev.xbutton.x - 4) / 44;
                            if (idx >= 0 && idx < term.ntabs) {
                                term.active = idx;
                                redraw();
                            } else if (idx == term.ntabs) {
                                new_tab();
                            }
                        }
                        break;
                    case SelectionNotify:        // paste arrived
                        if (paste_pending && ev.xselection.property != None) {
                            Atom type;
                            int fmt;
                            unsigned long n, bl, left;
                            unsigned char *data = NULL;
                            left = 65536;
                            if (XGetWindowProperty(term.dpy, term.win,
                                    sel_prop_atom, 0, left, False, XA_STRING,
                                    &type, &fmt, &n, &bl, &data) == Success &&
                                data && n > 0) {
                                Tab *t = &term.tabs[term.active];
                                paste_text(t, (const char *)data, n);
                            }
                            if (data) XFree(data);
                            XDeleteProperty(term.dpy, term.win, sel_prop_atom);
                            paste_pending = 0;
                        }
                        break;
                    case SelectionRequest: {     // someone wants our copy
                        XSelectionRequestEvent *r = &ev.xselectionrequest;
                        XSelectionEvent s;
                        memset(&s, 0, sizeof(s));
                        s.type = SelectionNotify;
                        s.display = r->display;
                        s.requestor = r->requestor;
                        s.selection = r->selection;
                        s.target = r->target;
                        s.time = r->time;
                        Atom prop = (r->property == None) ? r->target
                                                          : r->property;
                        if (r->target == XA_STRING)
                            XChangeProperty(term.dpy, r->requestor, prop,
                                            XA_STRING, 8, PropModeReplace,
                                            (unsigned char *)clip,
                                            (int)strlen(clip));
                        else
                            prop = None;
                        s.property = prop;
                        XSendEvent(term.dpy, r->requestor, False, 0,
                                   (XEvent *)&s);
                        XFlush(term.dpy);
                        break;
                    }
                    case SelectionClear:         // lost ownership: keep copy
                        break;
                    case ClientMessage:
                        if ((Atom)ev.xclient.data.l[0] == term.wm_delete) {
                            if (term.process_mode) {
                                for (int i = 0; i < term.ntabs; i++)
                                    if (tab_pid[i] > 0) kill(tab_pid[i], SIGKILL);
                            }
                            save_history();
                            XCloseDisplay(term.dpy);
                            return 0;
                        }
                        break;
                    }
                }
            }
        }
    }
    return 0;
}
