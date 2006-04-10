CC=gcc
CFLAGS=-pedantic -Wall -W -O
CPPFLAGS=

all: cDirectory.o ipc.o set_return_code_c.o \
	Clean\ System\ Files \
	Clean\ System\ Files/cDirectory.o \
	Clean\ System\ Files/ipc.o \
	Clean\ System\ Files/set_return_code_c.o

Clean\ System\ Files:
	mkdir "Clean System Files"

Clean\ System\ Files/cDirectory.o : cDirectory.c
	$(CC) -c $(CFLAGS) $< -o "$@"

Clean\ System\ Files/ipc.o : ipc.c
	$(CC) -c $(CFLAGS) $< -o "$@"

Clean\ System\ Files/set_return_code_c.o : set_return_code_c.c
	$(CC) -c $(CFLAGS) $< -o "$@"

