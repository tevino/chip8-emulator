#!/usr/bin/env python
# -*- coding: utf-8 -*-
import re
import sys
import time
import pyglet
import functools
from random import randint
from threading import Thread
from pyglet.gl import glRectf
from pyglet.window import key
from pyglet import clock

cycles_per_second = 60 * 2
pixel_size = 10


class Emulator(pyglet.window.Window):
    keymap = {
        key._0: 0,
        key._1: 1,
        key._2: 2,
        key._3: 3,
        key._4: 4,
        key._5: 5,
        key._6: 6,
        key._7: 7,
        key._8: 8,
        key._9: 9,
        key.A: 0xa,
        key.B: 0xb,
        key.C: 0xc,
        key.D: 0xd,
        key.E: 0xe,
        key.F: 0xf,
    }
    _memory = [0] * 4096   # 4096 bytes(4K) of memory
    _graphic_memory = []
    _keypad = [0] * 16      # keyboard

    fontset = [
        0xF0, 0x90, 0x90, 0x90, 0xF0,
        0x20, 0x60, 0x20, 0x20, 0x70,
        0xF0, 0x10, 0xF0, 0x80, 0xF0,
        0xF0, 0x10, 0xF0, 0x10, 0xF0,  # 3
        0x90, 0x90, 0xF0, 0x10, 0x10,
        0xF0, 0x80, 0xF0, 0x10, 0xF0,
        0xF0, 0x80, 0xF0, 0x90, 0xF0,  # 6
        0xF0, 0x10, 0x20, 0x40, 0x40,
        0xF0, 0x90, 0xF0, 0x90, 0xF0,
        0xF0, 0x90, 0xF0, 0x10, 0xF0,  # 9
        0xF0, 0x90, 0xF0, 0x90, 0x90,
        0xE0, 0x90, 0xE0, 0x90, 0xE0,
        0xF0, 0x80, 0x80, 0x80, 0xF0,  # C
        0xE0, 0x90, 0x90, 0x90, 0xE0,
        0xF0, 0x80, 0xF0, 0x80, 0xF0,
        0xF0, 0x80, 0xF0, 0x80, 0x80,  # F
    ]

    _registers = [0] * 16  # 16 registers, 1 byte each
    _address_i = 0         # the 16-bit address register I
    _program_counter = 0   # the 16-bit program counter
    _stack = list()        # stack
    _delay_timer = 0
    _sound_timer = 0
    _screen_changed = False

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.init_opcodes()
        self._program_counter = 0x200
        self._memory[0:len(self.fontset)] = self.fontset
        self.clear_graphic_memory()

    def init_opcodes(self):
        def op_00E0():
            self.clear_graphic_memory()

        def op_00EE():
            '''Return from a subroutine.
            The interpreter sets the program counter to the address at the top
            of the stack, then subtracts 1 from the stack pointer.
            '''
            self._program_counter = self._stack.pop()

        def op_1NNN(nnn):
            '''Jump to location nnn.
            The interpreter sets the program counter to nnn.
            '''
            self._program_counter = nnn

        def op_2NNN(nnn):
            '''Call subroutine at nnn.
            The interpreter increments the stack pointer, then puts the current
            PC on the top of the stack. The PC is then set to nnn.
            '''
            self._stack.append(self._program_counter)
            self._program_counter = nnn

        def op_3XNN(x, nn):
            '''Skip next instruction if Vx = NN.
            The interpreter compares register Vx to NN, and if they are
            equal, increments the program counter by 2.
            '''
            if self._registers[x] == nn:
                self._program_counter += 2

        def op_4XNN(x, nn):
            '''Skip next instruction if Vx != NN.
            The interpreter compares register Vx to NN, and if they are
            NOT equal, increments the program counter by 2.
            '''
            if self._registers[x] != nn:
                self._program_counter += 2

        def op_5XY0(x, y):
            '''Skip next instruction if Vx = Vy.
            The interpreter compares register Vx to register Vy, and if they
            are equal, increments the program counter by 2.
            '''
            if self._registers[x] == self._registers[y]:
                self._program_counter += 2

        def op_6XNN(x, nn):
            '''Set Vx = NN.
            The interpreter puts the value NN into register Vx.
            '''
            self._registers[x] = nn

        def op_7XNN(x, nn):
            '''Set Vx = Vx + NN.
            Adds the value NN to the value of register Vx,
            then stores the result in Vx.
            '''
            self._registers[x] += nn
            if self._registers[x] > 0xff:
                self._registers[x] %= 256

        def op_8XY0(x, y):
            '''Set Vx = Vy.
            Stores the value of register Vy in register Vx.
            '''
            self._registers[x] = self._registers[y]

        def op_8XY1(x, y):
            '''Set Vx = Vx OR Vy.
            Performs a bitwise OR on the values of Vx and Vy,
            then stores the result in Vx.
            '''
            self._registers[x] |= self._registers[y]

        def op_8XY2(x, y):
            '''Set Vx = Vx AND Vy.
            Performs a bitwise AND on the values of Vx and Vy,
            then stores the result in Vx.
            '''
            self._registers[x] &= self._registers[y]

        def op_8XY3(x, y):
            '''Set Vx = Vx XOR Vy.
            Performs a bitwise exclusive OR on the values of Vx and Vy,
            then stores the result in Vx.
            '''
            self._registers[x] ^= self._registers[y]

        def op_8XY4(x, y):
            '''Set Vx = Vx + Vy, set VF = carry.
            The values of Vx and Vy are added together.
            If the result is greater than 8 bits (i.e., > 255,)
            VF is set to 1, otherwise 0.
            Only the lowest 8 bits of the result are kept, and stored in Vx.
            '''
            self._registers[x] += self._registers[y]
            if self._registers[x] > 0xff:
                self._registers[x] %= 256
                self._registers[0xf] = 1
            else:
                self._registers[0xf] = 0

        def op_8XY5(x, y):
            '''VX = VX - VY, VF = not borrow'''
            if self._registers[x] >= self._registers[y]:
                self._registers[0xf] = 1
            else:
                self._registers[0xf] = 0
            self._registers[x] -= self._registers[y]
            if self._registers[x] < 0:
                self._registers[x] %= 256

        def op_8XY6(x, y):
            '''VX = VX SHR 1 (VX=VX/2), VF = carry'''
            self._registers[0xf] = self._registers[x] & 0x1
            self._registers[x] >>= 1

        def op_8XY7(x, y):
            '''VX = VY - VX, VF = not borrow '''
            if self._registers[y] >= self._registers[x]:
                self._registers[0xf] = 1
            else:
                self._registers[0xf] = 0
            self._registers[x] = self._registers[y] - self._registers[x]
            if self._registers[x] < 0:
                self._registers[x] %= 256

        def op_8XYE(x, y):
            '''VX = VX SHL 1 (VX=VX*2), VF = carry'''
            self._registers[x] <<= 1
            if self._registers[x] > 0xff:
                self._registers[0xf] = 1
                self._registers[x] %= 256
            else:
                self._registers[0xf] = 0

        def op_9XY0(x, y):
            '''Skips the next instruction if VX doesn't equal VY.'''
            if self._registers[x] != self._registers[y]:
                self._program_counter += 2

        def op_ANNN(nnn):
            '''Sets I to the address NNN.'''
            self._address_i = nnn

        def op_BNNN(nnn):
            '''Jumps to the address NNN plus V0.'''
            self._program_counter = nnn + self._registers[0]

        def op_CXNN(x, nn):
            '''Sets VX to a random number and NN.'''
            self._registers[x] = randint(0, 0xff) & nn

        def op_DXYN(x, y, n):
            '''Draws a sprite at coordinate (VX, VY)
            that has a width of 8 pixels and a height of N pixels.
            Each row of 8 pixels is read as bit-coded
            (with the most significant bit of each byte displayed on the left)
            starting from memory location I; I value doesn't change after the
            execution of this instruction. As described above, VF is set to 1
            if any screen pixels are flipped from set to unset when
            the sprite is drawn, and to 0 if that doesn't happen.
            '''
            self._registers[0xf] = 0
            vx = self._registers[x]
            vy = self._registers[y]
            i = self._address_i
            for row_i, row_bits in enumerate(self._memory[i:i + n]):
                _y = vy + row_i
                for column in range(8):
                    bit = int('{:08b}'.format(row_bits)[column])
                    _x = vx + column
                    if _x >= 64 or _y >= 32:
                        print('overflowed')
                        continue
                    self._graphic_memory[_x][_y] ^= bit
                    if self._graphic_memory[_x][_y]:
                        self._registers[0xf] = 1
            self._screen_changed = True

        def op_EX9E(x):
            '''
            Skips the next instruction if the key stored in VX is pressed.
            '''
            key = self._registers[x]
            if self._keypad[key]:
                self._program_counter += 2

        def op_EXA1(x):
            '''
            Skips the next instruction if the key stored in VX isn't pressed.
            '''
            key = self._registers[x]
            if not self._keypad[key]:
                self._program_counter += 2

        def op_FX07(x):
            '''Sets VX to the value of the delay timer.'''
            self._registers[x] = self._delay_timer

        def op_FX0A(x):
            '''A key press is awaited, and then stored in VX.'''
            for i, k in enumerate(self._keypad):
                if k:
                    self._registers[x] = i
                    return
            self._program_counter -= 2

        def op_FX15(x):
            '''Sets the delay timer to VX.'''
            self._delay_timer = self._registers[x]

        def op_FX18(x):
            '''Sets the sound timer to VX.'''
            self._sound_timer = self._registers[x]

        def op_FX1E(x):
            '''Adds VX to I.
            VF is set to 1 when range overflow (I+VX>0xFFF), and 0 when
            there isn't. This is undocumented feature of the Chip-8 and
            used by Spacefight 2019! game.'''
            self._address_i += self._registers[x]
            if self._address_i > 0xfff:
                self._registers[0xf] = 1
            else:
                self._registers[0xf] = 0

        def op_FX29(x):
            '''Sets I to the location of the sprite for the character in VX.
            Characters 0-F (in hexadecimal) are represented by a 4x5 font.'''
            self._address_i = self._registers[x] * 5

        def op_FX33(x):
            '''Stores the Binary-coded decimal representation of VX,
            with the most significant of three digits at the address in I,
            the middle digit at I plus 1, and the least significant digit
            at I plus 2. (In other words, take the decimal representation of
            VX, place the hundreds digit in memory at location in I, the tens
            digit at location I+1, and the ones digit at location I+2.)'''
            vx = self._registers[x]
            i = self._address_i
            self._memory[i] = (vx / 100)
            self._memory[i + 1] = (vx / 10) % 10
            self._memory[i + 2] = (vx % 100) % 10

        def op_FX55(x):
            '''Stores V0 to VX in memory starting at address I.'''
            size = x + 1
            i = self._address_i
            self._memory[i:i + size] = self._registers[0:size]
            # self._address_i += size

        def op_FX65(x):
            '''Fills V0 to VX with values from memory starting at address I.'''
            size = x + 1
            i = self._address_i
            self._registers[0:size] = self._memory[i:i + size]
            # self._address_i += size

        self.op_regex = []
        for func_name, func in locals().items():
            if func_name.startswith('op_'):
                r = func_name[3:]
                # address
                r = r.replace('NNN', '([0-9A-F]{3})')
                # 8-bit constant
                r = r.replace('NN', '([0-9A-F]{2})')
                # 4-bit constant
                r = r.replace('N', '([0-9A-F])')
                # 4-bit register identifier
                r = r.replace('X', '([0-9A-F])')
                r = r.replace('Y', '([0-9A-F])')
                self.op_regex.append((re.compile(r), func))

    def decode(self, opcode):
        for value in self.op_regex:
            r, func = value
            match = r.match('%0.4X' % opcode)
            if match:
                args = map(lambda x: int(x, 16), match.groups())
                return functools.partial(func, *args)
        print('no opcode matched: [%0.4X]', opcode)
        return lambda: None

    def _fetch_next_opcode(self):
        high, low = self._memory[
            self._program_counter:
            self._program_counter + 2
        ]
        self._program_counter += 2
        return (high << 8) | low

    def cycle(self):
        opcode = self._fetch_next_opcode()
        func = self.decode(opcode)
        func()
        if self._delay_timer > 0:
            self._delay_timer -= 1
        if self._sound_timer > 0:
            self._sound_timer -= 1
            if self._sound_timer == 0:
                pass
                # sound

    def clear_graphic_memory(self):
        # 2048(64x32) pixels of screen
        self._graphic_memory = [[0 for y in range(32)] for x in range(64)]
        self._screen_changed = True

    def load(self, filename):
        with open(filename, 'rb') as fl:
            binary = fl.read()
            self._memory[0x200:0x200 + len(binary)] = binary

    def on_key_press(self, symbol, modifiers):
        key = self.keymap.get(symbol)
        if key is not None:
            self._keypad[key] = 1

    def on_key_release(self, symbol, modifiers):
        key = self.keymap.get(symbol)
        if key is not None:
            self._keypad[key] = 0

    def on_draw(self, *args):
        # if self._screen_changed:
        self.clear()
        for x, row in enumerate(self._graphic_memory):
            for y, pt in enumerate(row):
                if pt:
                    self.draw_pixel(x, y)
            # self._screen_changed = False

    def draw_pixel(self, x, y):
        x_scaled = (x + 1) * pixel_size
        y_scaled = self.height - (y) * pixel_size
        glRectf(
            x_scaled - pixel_size, y_scaled,
            x_scaled, y_scaled - pixel_size
        )

    def start(self):
        def run():
            time_per_cycle = 1.0 / cycles_per_second
            while True:
                begin = time.time()
                self.cycle()
                sleep_time = time_per_cycle - (time.time() - begin)
                if sleep_time > 0:
                    time.sleep(sleep_time)
        td = Thread(target=run)
        td.daemon = True
        td.start()
        clock.schedule(self.on_draw)
        pyglet.app.run()


def main():
    if len(sys.argv) > 1:
        emu = Emulator(
            64 * pixel_size, 32 * pixel_size,
            caption='Chip-8 Emulator'
        )
        emu.load(sys.argv[1])
        emu.start()
    else:
        print('emu.py [ROM]')


if __name__ == '__main__':
    main()
