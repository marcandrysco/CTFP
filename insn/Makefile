CC = gcc
AS = as
LD = gcc
CFLAGS = -g -O2 -Wall
LDFLAGS = -lm

all: insn

insn: main.o asm.o
	$(LD) $(LDFLAGS) $^ -o $@

main.o: main.c Makefile
	$(CC) -c $(CFLAGS) $< -o $@

asm.o: asm.s
	$(AS) -c $< -o $@

run: all
	./insn
