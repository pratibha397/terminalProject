# Build Terminator from terminal.c
CC ?= gcc
CFLAGS ?= -std=c11 -O2 -Wall -Wextra
LDFLAGS ?=
LDLIBS ?= -lX11 -pthread -lrt

TARGET = terminator
SOURCE = terminal.c
OBJECT = terminal.o

.PHONY: all clean
all: $(TARGET)

$(TARGET): $(OBJECT)
	$(CC) $(LDFLAGS) -o $@ $(OBJECT) $(LDLIBS)

$(OBJECT): $(SOURCE)
	$(CC) $(CFLAGS) -c $(SOURCE) -o $(OBJECT)

clean:
	rm -f $(TARGET) $(OBJECT)
