#!/usr/bin/env python3
# Harmonarium - chord permutations written as LilyPond scores
# Copyright (C) 2026 Joshua Nichols
# Source code: https://github.com/joshdnichols/Harmonarium
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <https://www.gnu.org/licenses/>.
#
# The Harmonarium logo is licensed under the same terms. The scores
# Harmonarium writes are not covered by this license: they carry a CC0
# 1.0 Universal public domain dedication. Third-party material included
# with Harmonarium keeps its own license, such as the Academico font
# embedded in the control panel (SIL Open Font License 1.1) and the CC0
# badge printed on the scores (a Creative Commons trademark).
#
# SPDX-License-Identifier: GPL-3.0-or-later
"""
Harmonarium: chord permutations with a small control panel, written as LilyPond scores.
The companion to Melodarium: the same engine, but every permutation is an
ordering of chords instead of notes.

In the panel you choose:
  - a key (17 tonics) and mode (major, the three minors, the church modes)
  - chord size: triads, 7ths, 9ths, 11ths or 13ths, stacked in thirds from the key
  - extras: inversions, sus chords, add9, secondary dominants, borrowed chords,
    the Neapolitan, altered dominants - and any chord you add by hand
    (root, quality, optional slash bass)
  - which chords to use, and chords per permutation (2-12, slider)
  - repeats allowed / no chord twice in a row / each chord once
  - optional frame: every progression starts and/or ends on the tonic chord
  - labels: Roman numerals (below the staff), chord names (above), or both
  - key signature or an accidental on every note
  - placement: root position, or smooth voice leading (each chord takes the
    inversion and octave nearest the one before it)
  - clef, octave, staff size, systems per page, pages per PDF, file size, fonts
Every arrangement of the chosen chords is written as one stemless measure, a
measure number centred over every barline: measure N is always permutation N of
the full set, even in a ranged run. Files split at the size limit and are named
after their range (I.ii.IV-vi.V.I.ly). Each run's folder also gets master.ly and
engrave_all scripts, and, if you like, plain-text lists of every progression.
Progress is remembered in chord_progress.json, so a stopped run resumes.

Run:   python harmonarium.py
       The panel opens in the app's own window when pywebview is installed
       (pip install pywebview; on Windows it also needs Microsoft's WebView2 runtime,
       which Windows 11 and nearly all Windows 10 PCs have). Otherwise it opens in your
       browser. Add --browser to always use the browser.
Quit:  close the app window, press Quit in the panel, or (browser mode) close the
       terminal window or press Ctrl+C there. Progress is saved.

Start  - begin with the chosen settings, or continue after Pause / Stop
Pause  - hold in place (Start continues instantly)
Stop   - end this run and save to chord_progress.json (Start, or a later launch, resumes)
Reset  - forget progress so the settings can be changed

"""

import glob
import hashlib
import json
import math
import os
import re
import shutil
import struct
import subprocess
import sys
import tempfile
import threading
import time
import webbrowser
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

# ---------------- settings ----------------
WINDOWS_PATH_LIMIT = 255       # Windows' 260-character path limit, with a little room to spare
MIN_LEN, MAX_LEN = 2, 12        # slider range: chords per permutation
SPLIT_FROM = 9                  # from this many chords per measure, each measure is split over two lines
MIN_PAGES_PDF, MAX_PAGES_PDF = 1, 10000   # pages per PDF (each PDF is one LilyPond \\book)
MIN_KB, MAX_KB = 500, 1500      # slider range: max file size
MIN_STAFF, MAX_STAFF = 10, 30   # slider range: staff size (LilyPond's default is 20)
# Measure numbers: italic, relative size (scales with the staff size).
# -1.74 gives 9 pt at the default staff size of 20.
BAR_NUMBER_FONT_SIZE = -1.74
LABEL_FONT_SIZE = -1.5          # chord names and Roman numerals
CLEFS = {"treble": "G (treble)", "bass": "F (bass)", "tenor": "Tenor", "alto": "Alto"}
PITCHES = ["c,", "c", "c'", "c''", "c'''"]   # octave choices, low to high
PLACEMENTS = {"fixed": "Root position", "nearest": "Smooth voice leading"}
# notehead look only: every chord is still a quarter note, so rhythm and time signature stay the same
NOTEHEADS = {"filled": "Filled", "hollow": "Hollow", "whole": "Whole note"}
NOTEHEAD_LOG = {"hollow": 1, "whole": 0}   # LilyPond duration-log of the head drawn: 1 = half, 0 = whole
# scientific octave of each choice: c' is middle C (C4), "c" the C below it (C3)
OCTAVE_NUMBER = {"c,": 2, "c": 3, "c'": 4, "c''": 5, "c'''": 6}

# ---------------- chord theory ----------------
# Pitches are LilyPond names (Dutch: cis = C sharp, bes = B flat). Inside the program a
# chord tone is (semitones, letter steps) above the chord's root, so every note gets its
# proper spelling: a third above B is D sharp, never E flat.
LETTERS = "cdefgab"
LETTER_PC = [0, 2, 4, 5, 7, 9, 11]
MAJOR_SCALE = [0, 2, 4, 5, 7, 9, 11]   # Roman numerals are measured against the major scale
ROMAN = ["I", "II", "III", "IV", "V", "VI", "VII"]
TONICS = ["c", "cis", "des", "d", "dis", "ees", "e", "f", "fis", "ges", "g", "gis", "aes", "a",
          "ais", "bes", "b"]
MODES = {   # name: (label, semitones of the seven degrees, LilyPond key mode)
    "major":      ("Major", [0, 2, 4, 5, 7, 9, 11], "major"),
    "minor":      ("Natural minor", [0, 2, 3, 5, 7, 8, 10], "minor"),
    "harmonic":   ("Harmonic minor", [0, 2, 3, 5, 7, 8, 11], "minor"),
    "melodic":    ("Melodic minor", [0, 2, 3, 5, 7, 9, 11], "minor"),
    "dorian":     ("Dorian", [0, 2, 3, 5, 7, 9, 10], "dorian"),
    "phrygian":   ("Phrygian", [0, 1, 3, 5, 7, 8, 10], "phrygian"),
    "lydian":     ("Lydian", [0, 2, 4, 6, 7, 9, 11], "lydian"),
    "mixolydian": ("Mixolydian", [0, 2, 4, 5, 7, 9, 10], "mixolydian"),
    "locrian":    ("Locrian", [0, 1, 3, 5, 6, 8, 10], "locrian"),
}
SIZES = {"triads": ("Triads", 3), "sevenths": ("7ths", 4), "ninths": ("9ths", 5),
         "elevenths": ("11ths", 6), "thirteenths": ("13ths", 7)}
EXTRAS = {   # name: (label, what it adds)
    "inversions": ("Inversions", "every key chord in 1st and 2nd inversion (3rd too for 7ths); triads and 7ths only"),
    "sus": ("Sus chords", "sus2 and sus4 on each degree where both notes are in the key"),
    "add9": ("Add9", "major and minor triads with the key's 9th added"),
    "secondary": ("Secondary dominants", "V or V7 of each major and minor chord except the tonic"),
    "borrowed": ("Borrowed chords", "chords of the parallel major or minor that aren't in the key"),
    "neapolitan": ("Neapolitan", "♭II in root position and first inversion"),
    "altered": ("Altered dominants", "V7♭9, V7♯9 and V7♯5"),
    "augsixth": ("Augmented sixths", "Italian, French, German and Swiss sixths, built on ♭6"),
}
LABELS = {"roman": "Roman numerals", "names": "Chord names", "both": "Both"}
VOICINGS = {"close": "Close", "drop2": "Drop 2", "open": "Open"}
ACCIDENTALS = {"key": "Key signature", "every": "On every note"}

# chord tones: (semitones, letter steps) above the root
T = {"1": (0, 0), "b2": (1, 1), "2": (2, 1), "b3": (3, 2), "3": (4, 2), "4": (5, 3),
     "b5": (6, 4), "5": (7, 4), "#5": (8, 4), "6": (9, 5), "bb7": (9, 6), "b7": (10, 6),
     "7": (11, 6), "b9": (13, 8), "9": (14, 8), "#9": (15, 8), "11": (17, 10),
     "#11": (18, 10), "b13": (20, 12), "13": (21, 12)}
# chord qualities for chords you add yourself, and for the extras:
# name: (menu label, tones, chord-name suffix, upper-case numeral, numeral sign, numeral figure)
QUALITIES = {
    "maj":    ("Major", "1 3 5", "", True, "", ""),
    "min":    ("Minor", "1 b3 5", "m", False, "", ""),
    "dim":    ("Diminished", "1 b3 b5", "dim", False, "°", ""),
    "aug":    ("Augmented", "1 3 #5", "aug", True, "+", ""),
    "5":      ("Power chord (5)", "1 5", "5", True, "", "5"),
    "sus2":   ("sus2", "1 2 5", "sus2", True, "", "sus2"),
    "sus4":   ("sus4", "1 4 5", "sus4", True, "", "sus4"),
    "6":      ("6", "1 3 5 6", "6", True, "", "add6"),
    "m6":     ("m6", "1 b3 5 6", "m6", False, "", "add6"),
    "add9":   ("add9", "1 3 5 9", "add9", True, "", "add9"),
    "madd9":  ("m(add9)", "1 b3 5 9", "m(add9)", False, "", "add9"),
    "maj7":   ("maj7", "1 3 5 7", "maj7", True, "", "maj7"),
    "7":      ("7", "1 3 5 b7", "7", True, "", "7"),
    "m7":     ("m7", "1 b3 5 b7", "m7", False, "", "7"),
    "mmaj7":  ("m(maj7)", "1 b3 5 7", "m(maj7)", False, "", "maj7"),
    "m7b5":   ("m7♭5 (half-diminished)", "1 b3 b5 b7", "m7♭5", False, "ø", "7"),
    "dim7":   ("dim7", "1 b3 b5 bb7", "dim7", False, "°", "7"),
    "7sus4":  ("7sus4", "1 4 5 b7", "7sus4", True, "", "7sus4"),
    "7b5":    ("7♭5", "1 3 b5 b7", "7♭5", True, "", "7♭5"),
    "7#5":    ("7♯5", "1 3 #5 b7", "7♯5", True, "+", "7"),
    "maj7#5": ("maj7♯5", "1 3 #5 7", "maj7♯5", True, "+", "maj7"),
    "maj9":   ("maj9", "1 3 5 7 9", "maj9", True, "", "maj9"),
    "9":      ("9", "1 3 5 b7 9", "9", True, "", "9"),
    "m9":     ("m9", "1 b3 5 b7 9", "m9", False, "", "9"),
    "7b9":    ("7♭9", "1 3 5 b7 b9", "7(♭9)", True, "", "7(♭9)"),
    "7#9":    ("7♯9", "1 3 5 b7 #9", "7(♯9)", True, "", "7(♯9)"),
    "7#11":   ("7♯11", "1 3 5 b7 #11", "7(♯11)", True, "", "7(♯11)"),
    "7b13":   ("7♭13", "1 3 5 b7 b13", "7(♭13)", True, "", "7(♭13)"),
    "7alt":   ("7alt (♭9 ♯9 ♭13)", "1 3 b7 b9 #9 b13", "7alt", True, "", "7alt"),
    "maj7#11": ("maj7♯11", "1 3 5 7 #11", "maj7(♯11)", True, "", "maj7(♯11)"),
    "11":     ("11", "1 3 5 b7 9 11", "11", True, "", "11"),
    "m11":    ("m11", "1 b3 5 b7 9 11", "m11", False, "", "11"),
    "maj13":  ("maj13", "1 3 5 7 9 13", "maj13", True, "", "maj13"),
    "13":     ("13", "1 3 5 b7 9 13", "13", True, "", "13"),
    "m13":    ("m13", "1 b3 5 b7 9 11 13", "m13", False, "", "13"),
}

# augmented sixth chords: (numeral, tones above the ♭6 bass, chord-name suffix)
T6 = {"1": (0, 0), "3": (4, 2), "#4": (6, 3), "##4": (7, 3), "5": (7, 4), "#6": (10, 5)}
AUG_SIXTHS = [("It", "1 3 #6", "7(no5)"),          # ♭6 1 ♯4
              ("Fr", "1 3 #4 #6", "7♭5"),          # ♭6 1 2 ♯4
              ("Ger", "1 3 5 #6", "7"),            # ♭6 1 ♭3 ♯4
              ("Sw", "1 3 ##4 #6", "7")]           # ♭6 1 ♯2 ♯4 (German respelled, for major keys)

# stacked-third chords built from a key: names worked out from the intervals
TRIAD_TYPES = {(4, 7): ("", True, ""), (3, 7): ("m", False, ""), (3, 6): ("dim", False, "°"),
               (4, 8): ("aug", True, "+"), (4, 6): ("(♭5)", True, ""), (3, 8): ("m(♯5)", False, "")}
SEVENTH_TYPES = {   # (3rd, 5th, 7th): (name with {n}, numeral sign, figure with {n}, extensions stay "add")
    (4, 7, 11): ("maj{n}", "", "maj{n}", False), (4, 7, 10): ("{n}", "", "{n}", False),
    (3, 7, 10): ("m{n}", "", "{n}", False), (3, 7, 11): ("m(maj{n})", "", "maj{n}", False),
    (3, 6, 10): ("m{n}♭5", "ø", "{n}", False), (3, 6, 9): ("dim7", "°", "7", True),
    (4, 8, 11): ("maj{n}♯5", "+", "maj{n}", False), (4, 8, 10): ("{n}♯5", "+", "{n}", False),
    (4, 6, 10): ("{n}♭5", "", "{n}♭5", False), (4, 6, 11): ("maj{n}♭5", "", "maj{n}♭5", False),
    (3, 6, 11): ("dim(maj7)", "°", "maj7", True), (3, 8, 10): ("m{n}♯5", "", "{n}♯5", False),
}
EXTENSIONS = {8: {13: "♭9", 14: "9", 15: "♯9"}, 10: {16: "♭11", 17: "11", 18: "♯11"},
              12: {20: "♭13", 21: "13", 22: "♯13"}}
NATURAL_EXT = {8: 14, 10: 17, 12: 21}
INVERSION_FIGURES = {3: ["", "6", "64"], 4: ["", "65", "43", "42"]}


def split_pitch(tok):
    """'fis' -> (3, 1): letter index and accidental (+1 sharp, -1 flat)."""
    rest = tok[1:]
    return LETTERS.index(tok[0]), rest.count("is") - rest.count("es") - (1 if rest == "s" else 0)


def ly_name(letter, acc):
    return LETTERS[letter] + ("is" * acc if acc > 0 else "es" * -acc)


def disp_acc(acc):
    return {2: "𝄪", 1: "♯", 0: "", -1: "♭", -2: "𝄫"}.get(acc, "")


def disp_pitch(letter, acc):
    return LETTERS[letter].upper() + disp_acc(acc)


def norm_acc(diff):
    """A difference in semitones as an accidental between -6 and +5."""
    return (diff + 6) % 12 - 6


def tonic_label(tok):
    return disp_pitch(*split_pitch(tok))


class Chord:
    """One chord of the pool. root: (letter steps, semitones) above the tonic; tones:
    [(semitones, steps)] above the root; bass: index of the tone in the bass (an
    inversion), a (semitones, steps) bass note that isn't a chord tone, or None."""

    def __init__(self, group, root, tones, name_suffix, upper, sign, figure, figbass="",
                 bass=None, slash_roman="", numeral=None):
        self.group, self.root, self.tones = group, root, list(tones)
        self.numeral = numeral      # e.g. "V" for a secondary dominant (V7/ii)
        self.name_suffix, self.upper, self.sign, self.figure = name_suffix, upper, sign, figure
        self.figbass, self.bass, self.slash_roman = figbass, bass, slash_roman
        self.id = ""

    # ---- what the chord is ----
    def identity(self):
        bass = (self.tones[self.bass][0] % 12 if isinstance(self.bass, int)
                else self.bass[0] % 12 if self.bass else None)
        # spelling counts: a German and a Swiss sixth sound alike but are different chords
        return (self.root[0] % 7, self.root[1] % 12,
                frozenset((s % 12, st % 7) for s, st in self.tones), bass)

    def roman_parts(self):
        if self.numeral:
            return "", self.numeral
        steps, semis = self.root
        acc = norm_acc(semis - MAJOR_SCALE[steps % 7])
        numeral = ROMAN[steps % 7] if self.upper else ROMAN[steps % 7].lower()
        return disp_acc(acc).replace("𝄪", "♯♯").replace("𝄫", "♭♭"), numeral

    def roman_text(self):
        acc, numeral = self.roman_parts()
        return acc + numeral + self.sign + self.figure + self.figbass + self.slash_roman

    def name_text(self, tonic):
        tl, tacc = split_pitch(tonic)
        letter, acc = self.root_spelling(tonic)
        text = disp_pitch(letter, acc) + self.name_suffix
        bass = self.bass_tone()
        if bass is not None:
            bl = (letter + bass[1]) % 7
            bacc = norm_acc((LETTER_PC[letter] + acc + bass[0]) - LETTER_PC[bl])
            text += "/" + disp_pitch(bl, bacc)
        return text

    def bass_tone(self):
        if isinstance(self.bass, int):
            return self.tones[self.bass]
        return self.bass

    def root_spelling(self, tonic):
        tl, tacc = split_pitch(tonic)
        letter = (tl + self.root[0]) % 7
        pc = LETTER_PC[tl] + tacc + self.root[1]
        return letter, norm_acc(pc - LETTER_PC[letter])

    def slug(self):
        """File-name form of the Roman numeral: letters, digits and _ only."""
        out = self.roman_text()
        for a, b in (("♭", "b"), ("♯", "s"), ("°", "o"), ("ø", "h"), ("+", "x"), ("/", "_"),
                     ("(", ""), (")", ""), (" ", "")):
            out = out.replace(a, b)
        return re.sub(r"[^A-Za-z0-9_]", "", out) or "chord"

    # ---- notes ----
    def voicing(self, tonic, octave):
        """Close position from the root in the chosen octave (C to B), bass note at the
        bottom for an inversion or slash chord. Returns [(diatonic position, midi)]."""
        letter, acc = self.root_spelling(tonic)
        rpos = octave * 7 + letter
        rmidi = 12 * (octave + 1) + LETTER_PC[letter] + acc
        notes = [(rpos + st, rmidi + se) for se, st in self.tones]
        if isinstance(self.bass, int):
            b = notes[self.bass]
            rest = []
            for k, n in enumerate(notes):
                if k == self.bass:
                    continue
                while n[1] <= b[1]:
                    n = (n[0] + 7, n[1] + 12)
                rest.append(n)
            notes = [b] + sorted(rest, key=lambda n: n[1])
        elif self.bass:
            b = (rpos + self.bass[1], rmidi + self.bass[0])
            while b[1] >= notes[0][1]:
                b = (b[0] - 7, b[1] - 12)
            notes = [b] + notes
        if self.bass is not None:
            # an inversion or slash chord: its bass note in the chosen octave (C to B)
            shift = 0
            while notes[0][1] + shift >= 12 * (octave + 2):
                shift -= 12
            while notes[0][1] + shift < 12 * (octave + 1):
                shift += 12
            notes = [(p + 7 * shift // 12, m + shift) for p, m in notes]
        return notes

    def close_shapes(self, tonic, octave):
        """Every inversion in close position (chord tones folded into one octave), each
        as [(pos, midi)] built from the root in the chosen octave."""
        letter, acc = self.root_spelling(tonic)
        rpos = octave * 7 + letter
        rmidi = 12 * (octave + 1) + LETTER_PC[letter] + acc
        folded = {}
        for se, st in self.tones:
            folded.setdefault(se % 12, (se % 12, st % 7))
        tones = sorted(folded.values(), key=lambda t: (t[1], t[0]))
        shapes = []
        for r in range(len(tones)):
            order = tones[r:] + [(se + 12, st + 7) for se, st in tones[:r]]
            shapes.append([(rpos + st, rmidi + se) for se, st in order])
        return shapes


def stacked_name(semis):
    """Name parts for a chord of stacked thirds (semitones of root, 3rd, 5th, 7th, 9th...)."""
    third, fifth = semis[1], semis[2]
    if len(semis) == 3:
        name, upper, sign = TRIAD_TYPES.get((third, fifth), ("(?)", True, ""))
        return name, upper, sign, ""
    upper = third == 4
    base = SEVENTH_TYPES.get((third, fifth, semis[3]), ("{n}", "", "{n}", False))
    name, sign, fig, add_only = base
    n, alts = 7, []
    for k, se in enumerate(semis[4:]):
        steps = 8 + 2 * k
        label = EXTENSIONS[steps].get(se, "?")
        if not add_only and se == NATURAL_EXT[steps]:
            n = {8: 9, 10: 11, 12: 13}[steps]
        else:
            alts.append(label)
    tail = "(" + " ".join(alts) + ")" if alts else ""
    return name.format(n=n) + tail, upper, sign, fig.format(n=n) + tail


def scale_tone(mode, degree):
    s = MODES[mode][1]
    return s[degree % 7] + 12 * (degree // 7)


def diatonic(mode, size, group="Key"):
    out = []
    for i in range(7):
        semis = [scale_tone(mode, i + 2 * j) - scale_tone(mode, i) for j in range(size)]
        name, upper, sign, fig = stacked_name(semis)
        out.append(Chord(group, (i, scale_tone(mode, i)), [(se, 2 * j) for j, se in enumerate(semis)],
                         name, upper, sign, fig))
    return out


def from_quality(group, root, quality, **kw):
    q = QUALITIES[quality]
    return Chord(group, root, [T[t] for t in q[1].split()], q[2], q[3], q[4], q[5], **kw)


def interval_in_key(mode, degree, above):
    """Semitones from scale degree `degree` up to the degree `above` steps higher."""
    return scale_tone(mode, degree + above) - scale_tone(mode, degree)


def chord_pool(key, mode, size_name, extras=(), custom=()):
    """Every chord to choose from, in order: the key's own chords, then each extra,
    then chords added by hand. Each gets a unique id (its Roman numeral, file-name safe)."""
    size = SIZES[size_name][1]
    pool = diatonic(mode, size)
    tonic_major = MODES[mode][1][2] == 4
    triads = diatonic(mode, 3)
    if "inversions" in extras and size <= 4:
        for ch in diatonic(mode, size):
            for b in range(1, size):
                inv = Chord("Inversions", ch.root, ch.tones, ch.name_suffix, ch.upper, ch.sign,
                            "", INVERSION_FIGURES[size][b], bass=b)
                pool.append(inv)
    if "sus" in extras:
        for i in range(7):
            fifth = interval_in_key(mode, i, 4)
            if fifth != 7:
                continue
            if interval_in_key(mode, i, 1) == 2:
                pool.append(from_quality("Sus", (i, scale_tone(mode, i)), "sus2"))
            if interval_in_key(mode, i, 3) == 5:
                pool.append(from_quality("Sus", (i, scale_tone(mode, i)), "sus4"))
    if "add9" in extras:
        for i, tri in enumerate(triads):
            if interval_in_key(mode, i, 8) != 14:
                continue
            third = tri.tones[1][0]
            if tri.tones[2][0] == 7 and third in (3, 4):
                pool.append(from_quality("Add9", tri.root, "add9" if third == 4 else "madd9"))
    if "secondary" in extras:
        for i, tri in enumerate(triads):
            if i == 0 or tri.tones[2][0] != 7:      # not the tonic, not dim/aug chords
                continue
            root = ((i + 4) % 7, (scale_tone(mode, i) + 7) % 12)
            pool.append(from_quality("Secondary dominants", root, "7" if size >= 4 else "maj",
                                     slash_roman="/" + tri.roman_text(), numeral="V"))
    if "borrowed" in extras:
        for ch in diatonic("minor" if tonic_major else "major", size, "Borrowed"):
            pool.append(ch)
    if "neapolitan" in extras:
        q = "maj7" if size >= 4 else "maj"
        pool.append(from_quality("Neapolitan", (1, 1), q))
        pool.append(Chord("Neapolitan", (1, 1), [T[t] for t in QUALITIES[q][1].split()],
                          QUALITIES[q][2], True, "", "", INVERSION_FIGURES[min(size, 4)][1], bass=1))
    if "augsixth" in extras:
        # on the lowered 6th degree, which stays in the bass; the augmented 6th above it
        # (the raised 4th degree) resolves up, the bass down, both to the dominant.
        # Chord names give the dominant-7th-type chord they sound like.
        for numeral, tones, suffix in AUG_SIXTHS:
            pool.append(Chord("Augmented sixths", (5, 8), [T6[t] for t in tones.split()],
                              suffix, True, "+", "6", numeral=numeral))
    if "altered" in extras:
        for q in ("7b9", "7#9", "7#5"):
            pool.append(from_quality("Altered dominants", (4, 7), q))
    tl, tacc = split_pitch(key)
    for c in custom:
        try:
            rl, racc = split_pitch(c["root"])
            q = c["quality"]
            QUALITIES[q]
        except (KeyError, ValueError, TypeError, IndexError):
            continue
        steps = (rl - tl) % 7
        semis = (LETTER_PC[rl] + racc - LETTER_PC[tl] - tacc) % 12
        bass = None
        if c.get("bass"):
            bl, bacc = split_pitch(c["bass"])
            b_steps = (bl - rl) % 7
            b_semis = (LETTER_PC[bl] + bacc - LETTER_PC[rl] - racc) % 12
            tones = [T[t] for t in QUALITIES[q][1].split()]
            match = [k for k, (se, st) in enumerate(tones) if k and se % 12 == b_semis and st % 7 == b_steps]
            bass = match[0] if match else (b_semis, b_steps)
        ch = from_quality("Added by hand", (steps, semis), q, bass=bass)
        if bass is not None:
            bsemi = (semis + ch.bass_tone()[0]) % 12
            bstep = (steps + ch.bass_tone()[1]) % 7
            ch.slash_roman = "/" + disp_acc(norm_acc(bsemi - MAJOR_SCALE[bstep])) + str(bstep + 1)
        pool.append(ch)
    # drop repeats (a chord already in the pool), then give every chord a unique id
    seen, out, ids = set(), [], set()
    for ch in pool:
        ident = ch.identity()
        if ident in seen:
            continue
        seen.add(ident)
        base = ch.slug()
        cid, k = base, 2
        while cid in ids:
            cid, k = f"{base}_{k}", k + 1
        ch.id = cid
        ids.add(cid)
        out.append(ch)
    return out


def ly_pitch(pos, midi):
    """Absolute LilyPond pitch for a diatonic position (octave*7 + letter) and midi number."""
    letter, octave = pos % 7, pos // 7
    acc = midi - (12 * (octave + 1) + LETTER_PC[letter])
    return ly_name(letter, acc) + ("'" * (octave - 3) if octave >= 3 else "," * (3 - octave))


GLYPHS = {"♯": "\\noteSharp", "♭": "\\noteFlat", "𝄪": "\\noteDSharp", "𝄫": "\\noteDFlat"}


def mk_text(text):
    """Plain text as LilyPond markup, ASCII only: ♯ ♭ become music glyphs and any other
    non-ASCII character (°, ø) is written as its character code."""
    parts, cur = [], ""
    for ch in text:
        if ch in GLYPHS or ord(ch) > 127:
            if cur:
                parts.append('"' + cur + '"')
                cur = ""
            parts.append(GLYPHS.get(ch) or f"\\char ##x{ord(ch):04X}")
        else:
            cur += ch.replace('"', "'").replace("\\", "/")
    if cur:
        parts.append('"' + cur + '"')
    if not parts:
        return '""'
    return parts[0] if len(parts) == 1 else "\\concat { " + " ".join(parts) + " }"


def roman_markup(ch):
    """The Roman numeral: accidental and numeral, then sign and figure raised, a figured-bass
    inversion stacked (6 over 4), then any /target of a secondary dominant."""
    acc, numeral = ch.roman_parts()
    # ° and + sit beside the numeral at full size (the degree sign is already a raised
    # character, so superscript would lift it twice); ø goes up with the figure (viiø7)
    # (an augmented sixth's "+6" is one figure, the interval, so it stays raised: Ger+6)
    inline = ch.sign if ch.sign in ("°", "+") and ch.group != "Augmented sixths" else ""
    raised = ch.figure if inline else ch.sign + ch.figure
    parts = [mk_text(acc + numeral + inline)]
    if raised:
        parts.append("\\super " + mk_text(raised))
    if ch.figbass:
        if len(ch.figbass) == 1:
            parts.append("\\super " + mk_text(ch.figbass))
        else:
            parts.append("\\figureStack { " + " ".join(f'"{d}"' for d in ch.figbass) + " }")
    if ch.slash_roman:
        parts.append(mk_text(ch.slash_roman))
    return parts[0] if len(parts) == 1 else "\\concat { " + " ".join(parts) + " }"


def name_markup(ch, tonic):
    return mk_text(ch.name_text(tonic))


def apply_voicing(notes, voicing, keep_bass):
    """Re-space a close-position chord. Drop 2: the second note from the top goes down an
    octave. Open: every second note from the bottom (2nd, 4th, 6th) goes up an octave,
    so C E G becomes C G E. An inversion or slash chord keeps its bass note lowest
    (the bass moves down an octave if it has to)."""
    notes = sorted(notes, key=lambda n: n[1])
    if voicing == "close":
        return notes
    bass, upper = (notes[0], notes[1:]) if keep_bass else (None, notes)
    if voicing == "drop2" and len(upper) >= 3:
        k = len(upper) - 2
        upper = upper[:k] + [(upper[k][0] - 7, upper[k][1] - 12)] + upper[k + 1:]
    elif voicing == "open" and len(upper) >= 3:
        upper = [(p + 7, m + 12) if k % 2 else (p, m) for k, (p, m) in enumerate(upper)]
    upper = sorted(upper, key=lambda n: n[1])
    if bass is None:
        return upper
    while bass[1] >= upper[0][1]:
        bass = (bass[0] - 7, bass[1] - 12)
    return [bass] + upper


def smooth_voicing(ch, tonic, octave, prev, voicing="close"):
    """The voicing nearest the previous chord: every inversion in close position, a few
    octaves either way; the one whose notes move least wins (ties: the lower one).
    Slash chords and inversions keep their bass note at the bottom and only move by
    octaves. Kept within about an octave of the chosen octave."""
    if ch.bass is not None:
        base = ch.voicing(tonic, octave)
        shapes = [base]
    else:
        shapes = ch.close_shapes(tonic, octave)
    shapes = [apply_voicing(sh, voicing, ch.bass is not None) for sh in shapes]
    low, high = 12 * (octave + 1) - 8, 12 * (octave + 1) + 14   # where the bass may sit
    best, best_cost = None, None
    pm = [m for _, m in prev]
    for shape in shapes:
        for k in (-2, -1, 0, 1, 2):
            cand = [(p + 7 * k, m + 12 * k) for p, m in shape]
            if not low <= cand[0][1] <= high:
                continue
            cm = [m for _, m in cand]
            cost = (sum(min(abs(a - b) for b in pm) for a in cm)
                    + sum(min(abs(a - b) for b in cm) for a in pm))
            key = (cost, cand[0][1])
            if best is None or key < best_cost:
                best, best_cost = cand, key
    return best or apply_voicing(ch.voicing(tonic, octave), voicing, ch.bass is not None)

_os_replace = os.replace


def replace_file(src, dst):
    """os.replace, but patient on Windows: antivirus, search indexing or a sync folder can
    hold a file open for a moment, and Windows then refuses to replace it ("Access is
    denied", "being used by another process"). Retries for about half a minute."""
    delay = 0.05
    for attempt in range(60):
        try:
            return _os_replace(src, dst)
        except PermissionError:
            if attempt == 59:
                raise
            time.sleep(delay)
            delay = min(delay * 1.5, 1.0)


DEFAULT_SETTINGS = {"length": 4, "key": "c", "mode": "major", "size": "triads", "extras": [],
                    "custom": [], "chords": ["I", "ii", "iii", "IV", "V", "vi", "viio"],
                    "labels": "both", "accidentals": "key", "frame_start": "", "frame_end": "",
                    "voicing": "close", "double_bass": False, "chunk_labels": True,
                    "max_kb": 1000, "staff_size": 20,
                    "pages_per_pdf": 100, "repeat_mode": "all", "pdf_links": "off",
                    "systems_per_page": 8, "first_page_systems": 6, "text_font": "", "music_font": "", "lilypond": "2.26",
                    "outline_fonts": False, "save_to": "", "write_txt": False,
                    "clef": "treble", "pitch": "c'", "placement": "fixed", "noteheads": "filled"}



def app_folder():
    """The folder this program lives in: the .py file's folder, or - once packaged
    as an app - the folder holding the .exe (Windows) or the .app (Mac)."""
    if getattr(sys, "frozen", False):
        exe = os.path.abspath(sys.executable)
        parts = exe.split(os.sep)
        for k in range(len(parts) - 1, 0, -1):     # Mac: .../Name.app/Contents/MacOS/Name
            if parts[k].endswith(".app"):
                return os.sep.join(parts[:k]) or os.sep
        return os.path.dirname(exe)
    return os.path.dirname(os.path.abspath(__file__))


SCRIPT_DIR = app_folder()
# files packaged inside the app (PyInstaller puts them in sys._MEIPASS)
RESOURCE_DIR = getattr(sys, "_MEIPASS", SCRIPT_DIR)
# Mac app: things copied into Name.app/Contents/Resources after the build (LilyPond)
BUNDLE_RESOURCES = (os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(sys.executable)),
                                                  "..", "Resources"))
                    if getattr(sys, "frozen", False) and sys.platform == "darwin" else RESOURCE_DIR)
APP_NAME = "Harmonarium"


def _writable(folder):
    try:
        os.makedirs(folder, exist_ok=True)
        probe = os.path.join(folder, ".write-test")
        with open(probe, "w") as f:
            f.write("ok")
        os.remove(probe)
        return True
    except OSError:
        return False


def data_folder():
    """Where progress, settings, presets and (by default) the scores are kept.
    Running from the .py file, or a Windows app in a folder you can write to: next to
    the program. The Mac app (which lives in Applications), or a Windows app installed
    somewhere read-only like Program Files: Documents/Harmonarium."""
    if getattr(sys, "frozen", False):
        if sys.platform != "darwin" and _writable(SCRIPT_DIR):
            return SCRIPT_DIR
        docs = os.path.join(os.path.expanduser("~"), "Documents")
        return os.path.join(docs if os.path.isdir(docs) else os.path.expanduser("~"), APP_NAME)
    return SCRIPT_DIR


DATA_DIR = data_folder()
os.makedirs(DATA_DIR, exist_ok=True)
DEFAULT_PLACE = ("Next to this program" if DATA_DIR == SCRIPT_DIR
                 else "In Documents › " + APP_NAME if DATA_DIR.endswith(os.path.join("Documents", APP_NAME))
                 else "In your " + APP_NAME + " folder")
# Default save place is the folder this program is in; each run gets its own
# subfolder there (or in the folder chosen in the panel).
STATE_FILE = os.path.join(DATA_DIR, "chord_progress.json")  # memory of what was done last
LILYPOND_VERSIONS = {"2.26": "2.26 or newer", "2.24": "2.24"}   # syntax differs (fonts, spacing)
# Measure numbers. LilyPond counts measures in a number type that stops near 2.1 billion,
# so each \score block restarts LilyPond's count at 1 and this formatter adds the block's
# first permutation number using Scheme's unlimited whole numbers. Shown as:
#   below 1,000,000 ............ 57
#   below 1,000,000,000 ........ 12.345678M  (millions, six decimals)
#   from 1,000,000,000 up ...... 79 496 847 203 390 844 133 441 525 (groups of three)
PERM_BAR_NUMBER = r"""% measure numbers: the permutation's number in the full list (see the notes in the app)
#(define (permBarNumber base)
   (lambda (barnum measure-pos alt-number context)
     (if (and (ly:moment? measure-pos)
              (ly:moment<? (ly:make-moment 0) measure-pos))
         (make-null-markup)   ; a line that starts mid-measure: no number
         (let ((n (+ base barnum -1)))
           (cond
            ((< n 1000000) (make-simple-markup (number->string n)))
            ((< n 1000000000)
             (make-simple-markup
              (string-append (number->string (quotient n 1000000)) "."
                             (string-pad (number->string (remainder n 1000000)) 6 #\0) "M")))
            (else   ; groups of three digits with a small gap between them
             (let loop ((digits (number->string n)) (groups '()))
               (if (<= (string-length digits) 3)
                   (make-line-markup (cons digits groups))
                   (loop (substring digits 0 (- (string-length digits) 3))
                         (cons (substring digits (- (string-length digits) 3)) groups))))))))))

"""
SCORE_TARGET = 480              # measures per \score block: keeps LilyPond's memory use modest
NOTE_LENGTH = "4"               # LilyPond duration: 4 = quarter notes (one chord each)
PAGE_EXTRA_PT = 10              # extra space under the page header and above the footer (on top of LilyPond's own)
FIRST_PAGE_EXTRA_PT = 8         # extra space under the first page's titles (on top of LilyPond's own)
MIN_SYSTEMS, MAX_SYSTEMS = 1, 12  # slider range: lines of music per page (default 12)
MUSIC_FONT_WARNING = "for Lilypond version 2.24.x and above! Proceed at your own caution!"
OUTLINE_WARNING = ("Makes PDFs about 5 to 10 times larger: roughly 80-150 KB per page "
                   "instead of about 16 KB, so a 100-page PDF can reach 15 MB.")
# Music fonts that may only be used with "output to outline": Cadence is GPL without a
# font exception, so its font data is never embedded in the PDFs (only drawn shapes).
OUTLINE_REQUIRED = {"cadence"}
# Put at the top of a score file when "output to outline" is on. Music symbols (noteheads,
# clefs, accidentals...) are drawn as vector shapes, so the music font is never embedded;
# text (titles, measure numbers, footer) keeps its embedded font and stays selectable.
#  - LilyPond writes every music symbol with its named-glyph routine; this replaces that
#    routine with one that calls lyOG, a small PostScript procedure.
#  - lyOG traces the symbol's outline (charpath) and fills it, instead of showing it as
#    font text. It is handed to Ghostscript just before the PDF is made.
#  - Text uses a different routine, so it is untouched.
# (LilyPond's own gs-never-embed-fonts option is NOT used: it leaves fonts out of the
# PDF without drawing them, so noteheads, clefs and accidentals disappear.)
OUTLINE_SNIPPET = r"""% Output music to outline (music font: @FONT@): music symbols are drawn as vector shapes,
% so the music font is not embedded in the PDF. Text keeps its font and stays selectable.
#(let ((out (resolve-module '(lily output-ps)))
       (lily (resolve-module '(lily))))
   (if (not (module-variable lily 'music-outline-installed))
       (let* ((table (and (module-variable out 'stencil-dispatch-alist)
                          (module-ref out 'stencil-dispatch-alist)))
              (entry (and table (assq 'named-glyph table)))
              (font-cmd (and (module-variable out 'ps-font-command)
                             (module-ref out 'ps-font-command)))
              (lyOG (string-append
                     "/lyOGc 64 dict def /lyOG { currentfont lyOGc 1 index known not { "
                     "dup dup length 1 add dict begin { 1 index /FID ne { def } { pop pop } ifelse } forall "
                     "/Encoding 256 array def currentdict end /LyOutlineFont exch definefont "
                     "lyOGc 3 1 roll put currentfont } if lyOGc exch get gsave setfont "
                     "currentfont /Encoding get 0 3 -1 roll put "
                     "currentpoint newpath moveto (\\000) false charpath fill grestore } bind def ")))
         (module-define! lily 'music-outline-installed #t)
         (if (and entry font-cmd)
             (begin
               ;; music symbols: outline them (fall back to normal if lyOG is missing)
               (set-cdr! entry
                 (lambda (font glyph)
                   (format #f "~a /~a /lyOG where {pop lyOG} {glyphshow} ifelse\n"
                           (font-cmd font) glyph)))
               ;; hand the lyOG procedure to Ghostscript ahead of the score
               (for-each
                (lambda (name)
                  (let ((v (module-variable lily name)))
                    (if (and v (variable-bound? v))
                        (let ((run-gs (variable-ref v)))
                          (variable-set! v (lambda (args ps)
                                             (run-gs args (string-append lyOG ps))))))))
                '(ly:gs-api ly:gs-cli)))))))
"""
OUTLINE_MARK_RE = r"% Output music to outline \(music font: ([^)]*)\)"


def pdf_font_names(path):
    """Names of the fonts embedded in a PDF (subset prefixes like ABCDEF+ removed)."""
    try:
        with open(path, "rb") as f:
            data = f.read()
    except OSError:
        return set()
    return {m.decode("latin-1") for m in
            re.findall(rb"/FontName\s*/(?:[A-Z]{6}\+)?([^\s/\[\]<>()]+)", data)}


def music_font_embedded(path, music_font):
    """True if the PDF still embeds the music font (it should be outlines only)."""
    stem = (music_font or "emmentaler").lower()
    return any(n.lower() == stem or n.lower().startswith(stem + "-") for n in pdf_font_names(path))
CHUNK_DEPTH = 2                 # chunks group by the first 2 chords ("I ii x x")
ROW_DELAY = 0.0                 # seconds to wait after each bar (e.g. 0.005 to watch it run)
PORT = 8766                     # control panel address: http://127.0.0.1:8766 (Melodarium uses 8765)
# ------------------------------------------

# CC0 80x15 badge (Creative Commons "cc_zero.svg", small license badge from their
# official vocabulary design system), converted to vector EPS. It is saved in each
# run folder and placed in the footer with \epsfile.
CC0_EPS_NAME = "cc0-80x15.eps"
CC0_EPS = """%!PS-Adobe-3.0 EPSF-3.0
%%BoundingBox: 0 0 80 15
%%HiResBoundingBox: 0 0 80 15
%%Title: CC0 80x15 badge (Creative Commons)
%%Creator: converted from cc_zero.svg (creativecommons/vocabulary, license_badges/small)
%%Pages: 1
%%EndComments
save
10 dict begin
/m {moveto} bind def /l {lineto} bind def /c {curveto} bind def /h {closepath} bind def
newpath
0 15 m
80 15 l
80 0 l
0 0 l
h
1 setgray fill
newpath
80 15 m
80 0 l
0 0 l
0 15 l
80 15 l
79.25 14.25 m
0.75 14.25 l
0.75 0.75 l
79.25 0.75 l
79.25 14.25 l
h
0 setgray fill
newpath
22.797 13 m
23.8 11.405 24.39 9.523 24.39 7.499 c
24.39 5.476 23.801 3.595 22.798 2 c
80 2 l
80 13 l
22.797 13 l
h
12.42 12.969 m
9.283 12.969 8.494 10.01 8.494 7.5 c
8.494 4.99 9.281 2.031 12.42 2.031 c
15.557 2.031 16.344 4.99 16.344 7.5 c
16.344 10.01 15.557 12.969 12.42 12.969 c
h
12.42 10.906 m
12.547 10.906 12.662 10.886 12.772 10.859 c
12.999 10.666 13.108 10.396 12.893 10.021 c
10.803 6.183 l
10.738 6.67 10.729 7.145 10.729 7.5 c
10.729 8.605 10.807 10.906 12.42 10.906 c
h
13.982 9.137 m
14.093 8.549 14.109 7.934 14.109 7.5 c
14.109 6.395 14.033 4.094 12.42 4.094 c
12.293 4.094 12.176 4.106 12.066 4.133 c
12.046 4.139 12.027 4.147 12.005 4.154 c
11.974 4.164 11.939 4.174 11.907 4.185 c
11.548 4.339 11.321 4.615 11.647 5.105 c
13.982 9.137 l
h
0 setgray fill
newpath
21.229 11.152 m
20.764 12.304 20.086 13.324 19.194 14.218 c
18.907 14.504 18.607 14.759 18.302 15 c
14.594 15 l
15.842 14.652 16.961 13.991 17.948 13.002 c
18.684 12.266 19.247 11.426 19.632 10.486 c
20.017 9.546 20.21 8.55 20.21 7.5 c
20.21 5.316 19.464 3.506 17.983 2.059 c
17.212 1.313 16.348 0.739 15.387 0.342 c
15.043 0.199 14.693 0.091 14.341 0 c
18.233 0 l
18.569 0.257 18.897 0.529 19.205 0.834 c
20.1 1.705 20.775 2.705 21.226 3.834 c
21.691 4.977 21.919 6.197 21.919 7.5 c
21.92 8.789 21.691 10.01 21.229 11.152 c
h
6.957 2.025 m
6.211 2.771 5.635 3.615 5.228 4.552 c
4.832 5.503 4.628 6.482 4.628 7.499 c
4.628 8.528 4.831 9.515 5.228 10.454 c
5.634 11.403 6.21 12.257 6.957 13.015 c
7.916 13.996 9.021 14.654 10.268 15 c
6.58 15 l
6.289 14.765 6.004 14.516 5.732 14.238 c
4.816 13.324 4.117 12.279 3.631 11.113 c
3.156 9.959 2.92 8.756 2.92 7.5 c
2.92 6.232 3.156 5.029 3.631 3.887 c
4.106 2.745 4.795 1.717 5.699 0.801 c
5.994 0.51 6.305 0.248 6.623 0 c
10.503 0 l
10.158 0.088 9.817 0.191 9.484 0.328 c
8.547 0.723 7.705 1.289 6.957 2.025 c
h
0 setgray fill
newpath
30.514 7.264 m
30.235 7.031 29.836 6.914 29.317 6.914 c
28.324 6.914 l
28.324 5.197 l
27.333 5.197 l
27.333 9.972 l
29.383 9.972 l
29.856 9.972 30.232 9.849 30.513 9.603 c
30.794 9.357 30.935 8.975 30.935 8.459 c
30.934 7.896 30.794 7.497 30.514 7.264 c
h
29.753 8.983 m
29.626 9.089 29.449 9.142 29.222 9.142 c
28.324 9.142 l
28.324 7.736 l
29.222 7.736 l
29.45 7.736 29.626 7.794 29.753 7.908 c
29.879 8.022 29.942 8.204 29.942 8.452 c
29.942 8.701 29.879 8.878 29.753 8.983 c
h
31.733 9.972 m
32.748 9.972 l
32.748 7.039 l
32.748 6.711 32.786 6.472 32.864 6.321 c
32.984 6.053 33.247 5.92 33.651 5.92 c
34.053 5.92 34.315 6.054 34.435 6.321 c
34.512 6.471 34.551 6.711 34.551 7.039 c
34.551 9.972 l
35.565 9.972 l
35.565 7.037 l
35.565 6.529 35.486 6.135 35.329 5.851 c
35.036 5.332 34.476 5.074 33.651 5.074 c
32.825 5.074 32.264 5.333 31.969 5.851 c
31.812 6.134 31.733 6.529 31.733 7.037 c
31.733 9.972 l
h
40.085 9.463 m
40.231 9.26 40.304 9.017 40.304 8.734 c
40.304 8.442 40.23 8.208 40.083 8.031 c
40 7.931 39.879 7.841 39.719 7.759 c
39.962 7.671 40.146 7.53 40.27 7.338 c
40.394 7.146 40.457 6.913 40.457 6.639 c
40.457 6.356 40.386 6.102 40.244 5.878 c
40.154 5.729 40.041 5.604 39.906 5.502 c
39.754 5.385 39.574 5.306 39.367 5.262 c
39.159 5.219 38.934 5.198 38.692 5.198 c
36.54 5.198 l
36.54 9.972 l
38.848 9.972 l
39.43 9.963 39.842 9.793 40.085 9.463 c
h
37.492 9.143 m
37.492 8.09 l
38.652 8.09 l
38.86 8.09 39.028 8.129 39.157 8.208 c
39.287 8.287 39.351 8.427 39.351 8.627 c
39.351 8.85 39.265 8.996 39.094 9.067 c
38.947 9.117 38.759 9.142 38.531 9.142 c
37.492 9.142 l
h
37.492 7.3 m
37.492 6.027 l
38.651 6.027 l
38.858 6.027 39.019 6.055 39.134 6.111 c
39.343 6.215 39.447 6.414 39.447 6.708 c
39.447 6.956 39.346 7.127 39.143 7.22 c
39.03 7.272 38.871 7.298 38.665 7.301 c
37.492 7.301 l
h
41.313 9.972 m
42.311 9.972 l
42.311 6.056 l
44.695 6.056 l
44.695 5.198 l
41.313 5.198 l
41.313 9.972 l
h
46.275 5.197 m
45.284 5.197 l
45.284 9.972 l
46.275 9.972 l
46.275 5.197 l
h
47.665 9.473 m
48.05 9.866 48.539 10.063 49.133 10.063 c
49.928 10.063 50.509 9.799 50.876 9.272 c
51.079 8.976 51.188 8.679 51.203 8.381 c
50.205 8.381 l
50.142 8.61 50.06 8.783 49.961 8.9 c
49.783 9.107 49.52 9.211 49.171 9.211 c
48.816 9.211 48.535 9.065 48.33 8.773 c
48.125 8.481 48.022 8.066 48.022 7.531 c
48.022 6.996 48.13 6.594 48.346 6.328 c
48.563 6.061 48.838 5.928 49.172 5.928 c
49.514 5.928 49.775 6.042 49.954 6.272 c
50.054 6.395 50.136 6.58 50.201 6.826 c
51.192 6.826 l
51.106 6.305 50.888 5.883 50.537 5.556 c
50.186 5.229 49.735 5.067 49.186 5.067 c
48.506 5.067 47.972 5.288 47.583 5.728 c
47.194 6.17 47 6.777 47 7.548 c
47.002 8.379 47.224 9.021 47.665 9.473 c
h
54.797 9.868 m
55.132 9.758 55.403 9.556 55.61 9.262 c
55.777 9.025 55.89 8.768 55.951 8.491 c
56.012 8.214 56.042 7.951 56.042 7.701 c
56.042 7.066 55.914 6.528 55.659 6.088 c
55.313 5.494 54.779 5.197 54.057 5.197 c
51.998 5.197 l
51.998 9.972 l
54.057 9.972 l
54.354 9.967 54.601 9.933 54.797 9.868 c
h
52.968 9.143 m
52.968 6.027 l
53.89 6.027 l
54.361 6.027 54.69 6.259 54.875 6.723 c
54.977 6.978 55.027 7.282 55.027 7.633 c
55.027 8.119 54.951 8.492 54.798 8.752 c
54.645 9.012 54.343 9.143 53.889 9.143 c
52.968 9.143 l
h
60.466 5.621 m
60.106 5.25 59.584 5.064 58.902 5.064 c
58.22 5.064 57.698 5.25 57.338 5.621 c
56.855 6.077 56.612 6.733 56.612 7.591 c
56.612 8.466 56.854 9.122 57.338 9.561 c
57.698 9.932 58.22 10.118 58.902 10.118 c
59.584 10.118 60.106 9.932 60.466 9.561 c
60.947 9.123 61.188 8.466 61.188 7.591 c
61.188 6.733 60.947 6.077 60.466 5.621 c
h
59.842 6.347 m
60.074 6.639 60.191 7.053 60.191 7.591 c
60.191 8.126 60.075 8.54 59.842 8.833 c
59.611 9.126 59.297 9.271 58.902 9.271 c
58.507 9.271 58.191 9.125 57.956 8.834 c
57.721 8.542 57.603 8.128 57.603 7.59 c
57.603 7.052 57.72 6.638 57.956 6.346 c
58.191 6.055 58.507 5.909 58.902 5.909 c
59.297 5.909 59.61 6.056 59.842 6.347 c
h
65.116 9.972 m
66.552 9.972 l
66.552 5.198 l
65.623 5.198 l
65.623 8.427 l
65.623 8.52 65.624 8.65 65.626 8.817 c
65.628 8.985 65.629 9.114 65.629 9.205 c
64.725 5.198 l
63.755 5.198 l
62.857 9.205 l
62.857 9.114 62.858 8.985 62.86 8.817 c
62.863 8.65 62.864 8.52 62.864 8.427 c
62.864 5.198 l
61.934 5.198 l
61.934 9.972 l
63.385 9.972 l
64.254 6.218 l
65.116 9.972 l
h
68.84 9.972 m
69.969 9.972 l
71.658 5.198 l
70.576 5.198 l
70.262 6.179 l
68.503 6.179 l
68.18 5.197 l
67.136 5.197 l
68.84 9.972 l
h
68.774 7.001 m
69.997 7.001 l
69.395 8.88 l
68.774 7.001 l
h
73.175 5.197 m
72.184 5.197 l
72.184 9.972 l
73.175 9.972 l
73.175 5.197 l
h
74.093 9.972 m
75.139 9.972 l
77.034 6.643 l
77.034 9.972 l
77.964 9.972 l
77.964 5.198 l
76.967 5.198 l
75.024 8.586 l
75.024 5.198 l
74.094 5.198 l
74.094 9.972 l
h
1 setgray fill
end
restore
showpage
%%EOF
"""
BADGE_HEIGHT = 2.4             # staff spaces (the badge is 80 x 15, so about 12.8 wide)
COPYRIGHT_TEXT = "CC0 1.0 Universal (public domain dedication)"
CC0_DEED = "https://creativecommons.org/publicdomain/zero/1.0/"   # required with the CC0 badge

KB = 1000
STATE_VERSION = 1
FOOTER_RESERVE = 1500           # room kept for the closing part of each file
# Middle staff line for each clef: pitch of the invisible padding notes.
CLEF_MIDDLE = {"treble": "b'", "bass": "d", "alto": "c'", "tenor": "a"}


def clean_custom(raw_custom):
    """Chords added by hand: [{"root", "quality", "bass"}] with known names only."""
    out = []
    for c in raw_custom or []:
        if not isinstance(c, dict):
            continue
        root, q, bass = c.get("root"), c.get("quality"), c.get("bass") or ""
        if root in TONICS and q in QUALITIES and (not bass or bass in TONICS):
            out.append({"root": root, "quality": q, "bass": bass})
    return out[:60]


def pool_for(settings):
    return chord_pool(settings["key"], settings["mode"], settings["size"],
                      settings.get("extras", []), settings.get("custom", []))


def pool_json(raw):
    """The chords to choose from, for the panel."""
    key = raw.get("key") if raw.get("key") in TONICS else "c"
    mode = raw.get("mode") if raw.get("mode") in MODES else "major"
    size = raw.get("size") if raw.get("size") in SIZES else "triads"
    extras = [e for e in EXTRAS if e in (raw.get("extras") or [])]
    s = {"key": key, "mode": mode, "size": size, "extras": extras, "custom": clean_custom(raw.get("custom"))}
    plan_like = {"pitch": "c'", "labels": "both"}
    out = []
    for ch in pool_for(s):
        notes = ch.voicing(key, OCTAVE_NUMBER[plan_like["pitch"]])
        body = "<" + " ".join(ly_pitch(*n) for n in notes) + ">"
        out.append({"id": ch.id, "roman": ch.roman_text(), "name": ch.name_text(key), "group": ch.group,
                    "notes": len(notes),
                    # widest label in characters, per label choice (measures per line)
                    "chars": {"roman": len(ch.roman_text()), "names": len(ch.name_text(key)),
                              "both": max(len(ch.roman_text()), len(ch.name_text(key)))},
                    # bytes this chord takes in a score file, per label choice (for the size estimate)
                    "bytes": {"roman": len(body) + 18 + len(roman_markup(ch)),
                              "names": len(body) + 18 + len(name_markup(ch, key)),
                              "both": len(body) + 36 + len(roman_markup(ch)) + len(name_markup(ch, key))}})
    return {"chords": out, "tonic": out[0]["id"] if out else None,
            "key_label": tonic_label(key) + " " + MODES[mode][0].lower()}


def validate(raw):
    """Check settings sent from the panel. Returns (settings, error)."""
    try:
        length = int(raw["length"])
        max_kb = int(raw["max_kb"])
        staff_size = int(raw.get("staff_size", DEFAULT_SETTINGS["staff_size"]))
        systems = int(raw.get("systems_per_page", DEFAULT_SETTINGS["systems_per_page"]))
        first_systems = int(raw.get("first_page_systems", systems))
        pages_pdf = int(raw.get("pages_per_pdf", DEFAULT_SETTINGS["pages_per_pdf"]))
        text_font = str(raw.get("text_font", "") or "").strip()
        music_font = str(raw.get("music_font", "") or "").strip()
        lilypond = str(raw.get("lilypond", DEFAULT_SETTINGS["lilypond"]))
        chosen = set(raw["chords"])
        key, mode, size = raw.get("key", "c"), raw.get("mode", "major"), raw.get("size", "triads")
        extras = list(raw.get("extras") or [])
        custom = clean_custom(raw.get("custom"))
        labels = raw.get("labels", "both")
        accidentals = raw.get("accidentals", "key")
        frame_start, frame_end = raw.get("frame_start") or "", raw.get("frame_end") or ""
        voicing = raw.get("voicing", "close")
        double_bass = bool(raw.get("double_bass", False))
        chunk_labels = bool(raw.get("chunk_labels", True))
        save_to = str(raw.get("save_to", "") or "").strip()
        write_txt = bool(raw.get("write_txt", False))
        range_start = raw.get("range_start") or None
        range_end = raw.get("range_end") or None
        clef = raw.get("clef", DEFAULT_SETTINGS["clef"])
        pitch = raw.get("pitch", DEFAULT_SETTINGS["pitch"])
        placement = raw.get("placement", DEFAULT_SETTINGS["placement"])
        noteheads = raw.get("noteheads", "filled")
        repeat_mode = str(raw.get("repeat_mode", "all"))
        pdf_links = str(raw.get("pdf_links", "off"))
        outline_fonts = bool(raw.get("outline_fonts", False))
    except (KeyError, TypeError, ValueError):
        return None, "Invalid settings."
    if key not in TONICS:
        return None, "Choose a key."
    if mode not in MODES:
        return None, "Choose a mode."
    if size not in SIZES:
        return None, "Choose a chord size."
    if set(extras) - set(EXTRAS):
        return None, "Unknown extra chord option."
    extras = [e for e in EXTRAS if e in extras]
    if labels not in LABELS:
        return None, "Choose how chords are labelled."
    if accidentals not in ACCIDENTALS:
        return None, "Choose how accidentals are shown."
    if voicing not in VOICINGS:
        return None, "Choose a voicing."
    pool = chord_pool(key, mode, size, extras, custom)
    ids = [c.id for c in pool]
    # start / end chords: any chord in the list (older settings said True for the tonic)
    frame_start = ids[0] if frame_start is True else "" if frame_start is False else str(frame_start)
    frame_end = ids[0] if frame_end is True else "" if frame_end is False else str(frame_end)
    for label, f in (("start", frame_start), ("end", frame_end)):
        if f and f not in ids:
            return None, f"The {label} chord isn't in this key's list any more. Choose it again."
    if chosen - set(ids):
        return None, "Some ticked chords aren't in this key's list any more. Tick them again."
    chords = [c for c in ids if c in chosen]  # keep the list's order
    if save_to:
        save_to = os.path.abspath(os.path.expanduser(save_to))
        if not os.path.isdir(save_to):
            return None, f"Save folder not found: {save_to}"
        if not os.access(save_to, os.W_OK):
            return None, f"Can't write to the save folder: {save_to}"
    if not MIN_LEN <= length <= MAX_LEN:
        return None, f"Chords per permutation must be {MIN_LEN}-{MAX_LEN}."
    if not chords:
        return None, "Tick at least one chord."
    if pdf_links not in PDF_LINKS:
        return None, "Choose a PDF links option."
    if repeat_mode not in REPEAT_MODES:
        return None, "Unknown repeat option."
    if perm_count(len(chords), length, repeat_mode) == 0:
        return None, ("“Use each chord once” needs at least as many ticked chords "
                      "as chords per permutation." if repeat_mode == "once" else
                      "“No chord twice in a row” needs at least 2 ticked chords.")
    if clef not in CLEFS:
        return None, "Choose a clef."
    if pitch not in PITCHES:
        return None, "Choose an octave."
    if noteheads not in NOTEHEADS:
        return None, "Choose a notehead style."
    if placement not in PLACEMENTS:
        return None, "Choose a chord placement."
    if not MIN_KB <= max_kb <= MAX_KB:
        return None, f"File size must be {MIN_KB}-{MAX_KB} KB."
    if not MIN_STAFF <= staff_size <= MAX_STAFF:
        return None, f"Staff size must be {MIN_STAFF}-{MAX_STAFF}."
    if lilypond not in LILYPOND_VERSIONS:
        return None, "Choose a LilyPond version."
    if not MIN_PAGES_PDF <= pages_pdf <= MAX_PAGES_PDF:
        return None, f"Pages per PDF must be {MIN_PAGES_PDF}-{MAX_PAGES_PDF:,}."
    if not MIN_SYSTEMS <= systems <= MAX_SYSTEMS:
        return None, f"Systems per page must be {MIN_SYSTEMS}-{MAX_SYSTEMS}."
    if not MIN_SYSTEMS <= first_systems <= MAX_SYSTEMS:
        return None, f"Systems on the first page must be {MIN_SYSTEMS}-{MAX_SYSTEMS}."
    # LilyPond font names are case-sensitive: use the installed spelling ("Cadence" -> "cadence")
    installed = {f.lower(): f for f in ((_lp_info or {}).get("music_fonts") or [])}
    music_font = installed.get(music_font.lower(), music_font)
    if music_font.lower() in OUTLINE_REQUIRED:
        outline_fonts = True          # required for this font; can't be switched off
    for label, name in (("Text font", text_font), ("Music font", music_font)):
        if len(name) > 100 or any(ch in name for ch in '"\\\n'):
            return None, f"{label}: please use a plain font name (no quotes or backslashes)."
    for name, r in (("Starting", range_start), ("Ending", range_end)):
        if r is not None and (len(r) != length or any(t not in chords for t in r)):
            return None, f"{name} permutation must be {length} of the ticked chords."
        if r is not None and not perm_allowed(r, repeat_mode):
            return None, f"{name} permutation repeats a chord, which this setting doesn't allow."
    if range_start and range_end:
        idx = lambda r: rank([chords.index(t) for t in r], len(chords), length, repeat_mode)
        if idx(range_end) <= idx(range_start):
            return None, "Permutation not possible: the ending must come after the starting permutation."
    return {"length": length, "chords": chords, "max_kb": max_kb, "fit_pages": True,
            "key": key, "mode": mode, "size": size, "extras": extras, "custom": custom,
            "labels": labels, "accidentals": accidentals,
            "frame_start": frame_start, "frame_end": frame_end,
            "voicing": voicing, "double_bass": double_bass, "chunk_labels": chunk_labels,
            "range_start": list(range_start) if range_start else None,
            "range_end": list(range_end) if range_end else None,
            "save_to": save_to,
            "write_txt": write_txt, "staff_size": staff_size,
            "systems_per_page": systems, "first_page_systems": first_systems, "text_font": text_font, "music_font": music_font,
            "pages_per_pdf": pages_pdf,
            "lilypond": lilypond,
            "clef": clef, "pitch": pitch, "placement": placement, "noteheads": noteheads,
            "repeat_mode": repeat_mode,
            "pdf_links": pdf_links, "outline_fonts": outline_fonts}, None


def fit_json(raw):
    """How many systems fit on the first page and on the others with these settings
    (for the panel's warning under the page sliders)."""
    try:
        raw = dict(raw, systems_per_page=MAX_SYSTEMS, first_page_systems=MAX_SYSTEMS,
                   save_to="", range_start=None, range_end=None)
        settings, err = validate(raw)
        if err:
            return {"ok": False}
        plan = Plan(dict(settings, fit_pages=False))
        return {"ok": True, "first": plan.systems_that_fit(True), "rest": plan.systems_that_fit(False)}
    except Exception:
        return {"ok": False}


PDF_LINKS = {"off": "No links", "notes": "Links on chords", "all": "All links"}
# Title-block text widths (measured with LilyPond 2.26 at staff size 20; they scale with
# the staff size). Text wider than TEXT_LINE_PT is broken into centred lines.
DASH = "\\char ##x2013 "        # the en dash that starts a title / subtitle suffix
TEXT_LINE_PT = 480            # the music line is about 516 pt wide on letter paper
TITLE_PT_PER_CHAR = 10.0
SUBTITLE_PT_PER_CHAR = 5.9
PIECE_PT_PER_CHORD = 30.0     # the range line, per chord label
SUBTITLE_LEADING = 2.8        # baseline to baseline of a subtitle on several lines (LilyPond's usual: 3)
SUBTITLE_GAP_EXTRA_PT = 6     # extra space between the subtitle and the range line
SUBTITLE_LIST_MAX = 16        # list the chords in the subtitle up to this many, else just count them
# added to the end of the title / subtitle on every score (LilyPond markup; the files
# are plain ASCII, so the en dash is written as its character code)
TITLE_SUFFIX = {"norepeat": '\\char ##x2013 "No Chord Twice in a Row"',
                "once": '\\char ##x2013 "Using Each Chord Once"'}
SUBTITLE_SUFFIX = {"nearest": '\\char ##x2013 "smooth voice leading"',
                   "fixed": '\\char ##x2013 "root position"'}
REPEAT_MODES = {"all": "Repeats allowed",
                "norepeat": "No chord twice in a row",
                "once": "Use each chord once"}


def perm_count(n, k, mode):
    """How many permutations of k chords chosen from n, in a given mode."""
    if mode == "once":
        return math.perm(n, k) if k <= n else 0
    if mode == "norepeat":
        return n * (n - 1) ** (k - 1)   # 0 when only one chord is ticked
    return n ** k


def tail_count(n, k, j, mode):
    """How many ways to finish a permutation once its first j chords are chosen."""
    if mode == "once":
        return math.perm(n - j, k - j)
    if mode == "norepeat":
        return (n - 1) ** (k - j)
    return n ** (k - j)


def unrank(i, n, k, mode):
    """The i-th permutation (in the order of the chord list), as positions."""
    out, prev, avail = [], None, list(range(n))
    for pos in range(k):
        r, i = divmod(i, tail_count(n, k, pos + 1, mode))
        if mode == "once":
            d = avail.pop(r)
        elif mode == "norepeat":
            d = r if prev is None or r < prev else r + 1   # skip the previous chord
        else:
            d = r
        out.append(d)
        prev = d
    return out


def rank(digits, n, k, mode):
    """Position of a permutation (given as chord positions) in list order."""
    i, prev, avail = 0, None, list(range(n))
    for pos, d in enumerate(digits):
        if mode == "once":
            r = avail.index(d)
            avail.remove(d)
        elif mode == "norepeat":
            r = d if prev is None or d < prev else d - 1
        else:
            r = d
        i += r * tail_count(n, k, pos + 1, mode)
        prev = d
    return i


def perm_allowed(tokens, mode):
    if mode == "once":
        return len(set(tokens)) == len(tokens)
    if mode == "norepeat":
        return all(a != b for a, b in zip(tokens, tokens[1:]))
    return True


CLEF_POS = {"treble": 34, "bass": 22, "alto": 28, "tenor": 26}   # middle line: octave*7 + letter
LABEL_GAP_ABOVE = 1.3         # staff spaces from the highest note to the chord names' baseline
LABEL_GAP_BELOW = 2.9         # staff spaces from the lowest note to the numerals' baseline
BARNUMBER_Y = 2.7             # measure numbers' baseline: just above the top staff line, by the barline
MARK_ABOVE_NAMES = 2.0        # chunk labels' baseline, staff spaces above the chord names
PAGE_SYSTEM_ROOM_PT = 740     # letter page: room for the systems and their labels (measured)
TITLE_BLOCK_SS = 7.4          # first page: one line each of title, subtitle and range line, staff spaces
TITLE_LINE_SS = 4.0           # each further line of the title
SUBTITLE_LINE_SS = 3.2        # each further line of the subtitle
PIECE_LINE_SS = 3.0           # the range line on two lines
NAMES_UNDER_TITLE_SS = 3.1    # chord names above the first system need extra room under the titles
FIT_SAFETY_SS = 0.25          # added to each system when counting, so a page is never overfull
SYSTEM_GAP = 1.5              # staff spaces of clear room between one line's labels and the next line's
LABEL_PT_PER_CHAR = 5.0      # chord labels at staff size 20, per character
LINE_ROOM_PT = 470           # room for chords on a line (about 516 pt, less clef and key)


def bars_per_system(chords, label_chars=0, staff_size=20):
    """Measures per line, by chords per measure: 2: 4 measures; 3-4: 2; 5 or more: 1.
    Fewer when the widest chord label wouldn't fit under every chord."""
    bars = 4 if chords <= 2 else 2 if chords <= 4 else 1
    per_chord = (label_chars * LABEL_PT_PER_CHAR + 6) * staff_size / 20
    while bars > 1 and bars * chords * per_chord > LINE_ROOM_PT:
        bars //= 2
    return bars


class Plan:
    """Everything derived from one set of settings."""

    PITCH_TAG = {"c,": "c2", "c": "c3", "c'": "c4", "c''": "c5", "c'''": "c6"}  # for folder names

    def __init__(self, settings):
        self.key = settings.get("key", "c")
        self.mode_name = settings.get("mode", "major")
        self.size = settings.get("size", "triads")
        self.labels = settings.get("labels", "both")
        self.accidentals = settings.get("accidentals", "key")
        pool = pool_for(settings)
        self.chords = {c.id: c for c in pool}
        self.tonic_chord = pool[0].id
        self.notes = list(settings["chords"])        # the chords being permuted, in list order
        self.length = settings["length"]
        fs, fe = settings.get("frame_start") or "", settings.get("frame_end") or ""
        fs = self.tonic_chord if fs is True else fs if fs in self.chords else ""   # older runs: True
        fe = self.tonic_chord if fe is True else fe if fe in self.chords else ""
        self.frame_before = [fs] if fs else []
        self.frame_after = [fe] if fe else []
        self.voicing = settings.get("voicing", "close")
        self.double_bass = bool(settings.get("double_bass", False))
        self.chunk_labels = bool(settings.get("chunk_labels", True))
        self.bar_chords = self.length + len(self.frame_before) + len(self.frame_after)
        self.max_bytes = settings["max_kb"] * KB
        self.clef = settings.get("clef", "treble")
        self.pitch = settings.get("pitch", "c'")
        self.octave = OCTAVE_NUMBER[self.pitch]
        self.placement = settings.get("placement", "fixed")
        self.noteheads = settings.get("noteheads", "filled")
        self.staff_size = int(settings.get("staff_size", 20))
        self.systems_per_page = int(settings.get("systems_per_page", 8))
        # the first page of every PDF also holds the title block, so it can have fewer systems
        self.first_page_systems = int(settings.get("first_page_systems", self.systems_per_page))
        self.bars_per_system = bars_per_system(
            self.bar_chords, max(self.label_chars(t) for t in self.notes + self.frame_before + self.frame_after),
            self.staff_size)   # measures per line
        self.text_font = settings.get("text_font") or ""
        self.music_font = settings.get("music_font") or ""
        self.outline_fonts = (bool(settings.get("outline_fonts"))
                              or self.music_font.lower() in OUTLINE_REQUIRED)
        self.lilypond = settings.get("lilypond", "2.26")
        self.version = "2.26.0" if self.lilypond == "2.26" else "2.24.0"
        self.mode = settings.get("repeat_mode", "all")
        # from SPLIT_FROM chords per measure each measure is split over two lines
        self.split_at = (self.bar_chords + 1) // 2 if self.bar_chords >= SPLIT_FROM else 0
        self._voicing_cache = {}
        self._label_cache = {}
        self._bar_notes = {}         # voicings of the current line's measures
        self.name_y, self.roman_y = self.label_baselines()
        # No more systems on a page than fit with this run's label heights: a page asked
        # to hold more would spill its last systems onto a page of their own. (Runs from
        # before this check resume exactly as they were laid out.)
        self.asked_systems = (self.systems_per_page, self.first_page_systems)
        self.fit_note = ""
        if settings.get("fit_pages"):
            self.systems_per_page = min(self.systems_per_page, self.systems_that_fit(False))
            self.first_page_systems = min(self.first_page_systems, self.systems_that_fit(True))
            if (self.systems_per_page, self.first_page_systems) != self.asked_systems:
                self.fit_note = (f"With these chords' labels only {self.first_page_systems} system(s) fit on "
                                 f"the first page and {self.systems_per_page} on the others, so the scores "
                                 "use that many.")
        # Page breaks are placed by this program (fast, low-memory page layout),
        # and each \score holds whole pages, about SCORE_TARGET measures.
        # From SPLIT_FROM chords per measure each measure is split evenly over two lines
        # (no barline at the split), so a page holds half as many measures.
        per_page = lambda systems: (max(1, systems // 2) if self.split_at
                                    else systems * self.bars_per_system)
        self.measures_per_page = per_page(self.systems_per_page)        # pages after the first
        self.first_page_measures = per_page(self.first_page_systems)    # each PDF's first page
        # Each PDF is a LilyPond \\book of pages_per_pdf pages. Inside it the music is in
        # \\score blocks of whole pages (about SCORE_TARGET measures) that divide the
        # book exactly, so books always end on a block boundary.
        self.pages_per_pdf = int(settings.get("pages_per_pdf", 100))
        target = max(1, round(SCORE_TARGET / self.measures_per_page))
        block_pages = max(d for d in range(1, min(target, self.pages_per_pdf) + 1)
                          if self.pages_per_pdf % d == 0)
        # a book's first \score block starts with its (shorter or longer) first page
        self.score_measures = self.measures_per_page * block_pages
        self.first_score_measures = self.first_page_measures + self.measures_per_page * (block_pages - 1)
        self.book_measures = self.first_page_measures + self.measures_per_page * (self.pages_per_pdf - 1)
        widest_label = max(len(self.mk_chord(t)) for t in self.notes)
        self.piece_room = (widest_label + 1) * self.length + 48   # space reserved for "to <last>"
        # space reserved for each book's  \\bookOutputName "first-last"
        self.book_room = 2 * self.length * (max(len(n) for n in self.notes) + 1) + 24
        self.base = len(self.notes)
        self.mode = settings.get("repeat_mode", "all")
        self.pdf_links = settings.get("pdf_links", "off")
        self.total = perm_count(self.base, self.length, self.mode)   # size of the full set
        # Optional range: first and last permutation to write (inclusive).
        rs, re_ = settings.get("range_start"), settings.get("range_end")
        self.first = self.index_of(rs) if rs else 0
        self.last = self.index_of(re_) if re_ else self.total - 1
        self.count = self.last - self.first + 1
        self.partial = self.count != self.total
        self.depth = min(CHUNK_DEPTH, self.length - 1)
        self.chunk_size = tail_count(self.base, self.length, self.depth, self.mode)
        self.out_dir = os.path.join(settings.get("save_to") or DATA_DIR,
                                    settings.get("folder_name") or self.folder_name(settings))
        self.working = os.path.join(self.out_dir, "_in_progress.ly")
        self.write_txt = bool(settings.get("write_txt", False))
        self.txt_working = os.path.join(self.out_dir, "_in_progress.txt")
        self.index_path = os.path.join(self.out_dir, "index.csv")
        # File names are "first-last". When that would make paths too long for Windows,
        # the last permutation is shortened to its final chords ("tail"), like a page range
        # 1234-56, and files also close wherever the chords before the tail change, so the
        # tail always identifies the last permutation. Kept in the settings for resuming.
        self.name_tail = settings.get("name_tail") or self.fitting_tail(settings["chords"])

    def folder_name(self, settings):
        """The run folder's name, from the settings: length, key, chord size, the chords
        (or, when that's long, their count and a short fingerprint), clef and octave."""
        chords = ".".join(self.notes)
        if len(chords) > 48:
            digest = hashlib.sha1(chords.encode("ascii")).hexdigest()[:6]
            chords = f"{len(self.notes)}chords-{digest}"
        rng = ""
        if self.partial:
            rng = f"-from-{self.first + 1}-to-{self.last + 1}"
            if len(str(self.last + 1)) > 9:
                rng = f"-from-{self.first + 1}-count-{self.count}"
        return (f"len{self.length}-{self.key}-{self.mode_name}-{self.size}-{chords}"
                + f"-{self.clef}-{self.PITCH_TAG[self.pitch]}"
                + {"norepeat": "-norepeat", "once": "-once"}.get(self.mode, "")
                + (f"-from-{self.frame_before[0]}" if self.frame_before else "")
                + (f"-to-{self.frame_after[0]}" if self.frame_after else "")
                + (f"-{self.voicing}" if self.voicing != "close" else "")
                + ("-bass8" if self.double_bass else "")
                + ("-voiceleading" if self.placement == "nearest" else "")
                + (f"-{self.noteheads}" if self.noteheads != "filled" else "")
                + {"roman": "-roman", "names": "-names"}.get(self.labels, "")
                + ("-allacc" if self.accidentals == "every" else "")
                + (f"-staff{self.staff_size}" if self.staff_size != 20 else "") + rng)

    def fitting_tail(self, chords):
        """How many final chords of the last permutation fit in file names (all of them if
        the full name fits; 0 if even one doesn't)."""
        if os.name != "nt":
            return self.length
        widest = max(len(n) for n in chords) + 1
        fixed = len(os.path.abspath(self.out_dir)) + 1 + self.length * widest + 1 + 4  # dir\first-....pdf
        room = WINDOWS_PATH_LIMIT - fixed
        return max(0, min(self.length, room // widest))

    @property
    def short_names(self):
        return self.name_tail < self.length

    def range_name(self, first, last):
        """File name for permutations first..last: 'first-last', or 'first-tail' when shortened."""
        tail = self.tokens_at(last)[self.length - self.name_tail:]
        return self.name_at(first) + "-" + ".".join(tail)

    def tail_boundary(self, i):
        """True if permutation i starts a new block of the chords before the tail (shortened
        names only): files and text lists then close before i."""
        if not self.short_names or i <= self.first:
            return False
        keep = self.length - self.name_tail
        return self.tokens_at(i)[:keep] != self.tokens_at(i - 1)[:keep]

    def book_pages(self, measures):
        """Pages used by the first `measures` measures of one book (PDF)."""
        if measures <= 0:
            return 0
        rest = measures - self.first_page_measures
        return 1 + (-(-rest // self.measures_per_page) if rest > 0 else 0)

    def file_pages(self, measures):
        """Pages used by a score file of `measures` measures (whole books, then the rest)."""
        full, rest = divmod(measures, self.book_measures)
        return full * self.pages_per_pdf + self.book_pages(rest)

    def page_ends_after(self, bar_in_book):
        """True if measure number bar_in_book (1 = the book's first) ends a page."""
        if bar_in_book <= self.first_page_measures:
            return bar_in_book == self.first_page_measures
        return (bar_in_book - self.first_page_measures) % self.measures_per_page == 0

    def index_of(self, tokens):
        if self.mode != "all":
            return rank([self.notes.index(t) for t in tokens], self.base, self.length, self.mode)
        i = 0
        for t in tokens:
            i = i * self.base + self.notes.index(t)
        return i

    def tokens_at(self, i):
        if self.mode != "all":
            return [self.notes[d] for d in unrank(i, self.base, self.length, self.mode)]
        parts = []
        for _ in range(self.length):
            i, r = divmod(i, self.base)
            parts.append(self.notes[r])
        return parts[::-1]

    def label_chars(self, tok):
        """Width of a chord's widest label, in characters (names and numerals sit on
        different sides of the staff, so with both the wider one counts)."""
        ch = self.chords[tok]
        return max(len(ch.name_text(self.key)) if self.labels != "roman" else 0,
                   len(ch.roman_text()) if self.labels != "names" else 0)

    def label(self, tok):
        """A chord as text, in the chosen labelling ("I", "C", or "I (C)")."""
        ch = self.chords[tok]
        if self.labels == "names":
            return ch.name_text(self.key)
        if self.labels == "roman":
            return ch.roman_text()
        return f"{ch.roman_text()} ({ch.name_text(self.key)})"

    def line_at(self, i):
        """One progression as text, frame chords included: 'I ii V I'."""
        toks = self.frame_before + self.tokens_at(i) + self.frame_after
        if self.labels == "both":
            return (" ".join(self.chords[t].roman_text() for t in toks) + "  |  "
                    + " ".join(self.chords[t].name_text(self.key) for t in toks))
        return " ".join(self.label(t) for t in toks)

    def name_at(self, i):
        """File-name form: the chord ids joined by dots, e.g. 'I.ii.V7.I'."""
        return ".".join(self.tokens_at(i))

    def chunk_label(self, i):
        if i > self.last:
            return "done"
        toks = self.tokens_at(i)[:self.depth]
        text = [self.chords[t].name_text(self.key) if self.labels == "names"
                else self.chords[t].roman_text() for t in toks]
        return " ".join(text + ["x"] * (self.length - self.depth))

    # ---- LilyPond pieces ----
    def mk_chord(self, tok):
        """A chord's label as markup for titles and chunk labels (Roman numerals unless
        only chord names were chosen)."""
        ch = self.chords[tok]
        return name_markup(ch, self.key) if self.labels == "names" else roman_markup(ch)

    def mk_perm(self, tokens):
        return "\\line { " + " ".join(
            self.mk_chord(t) if t != "x" else "\\anyNote" for t in tokens) + " }"

    def fonts_block(self):
        """Text and/or music font, in the syntax of the chosen LilyPond version."""
        if not (self.text_font or self.music_font):
            return ""
        if self.lilypond == "2.26":
            lines = []
            if self.music_font:
                lines += [f"  % {MUSIC_FONT_WARNING}",
                          f'  property-defaults.fonts.music = "{self.music_font}"']
            if self.text_font:
                lines += [f'  property-defaults.fonts.serif = "{self.text_font}"']
            return "\n".join(lines) + "\n"
        # LilyPond 2.24: one set-global-fonts call sets text and music fonts together
        lines = ["  #(define fonts", "     (set-global-fonts"]
        if self.music_font:
            lines += [f"       #:music \"{self.music_font}\"   ; {MUSIC_FONT_WARNING}",
                      f"       #:brace \"{self.music_font}\""]
        if self.text_font:
            lines += [f"       #:roman \"{self.text_font}\""]
        lines += ["       #:factor (/ staff-height pt 20)))"]
        return "\n".join(lines) + "\n"

    def spacing_block(self):
        # LilyPond measures these gaps in staff spaces; a staff space is staff-size/4 pt
        ss = self.staff_size / 4.0
        g = lambda pt: f"{pt / ss:.2f}".rstrip("0").rstrip(".")
        return (
            "  % values are in staff spaces; each is LilyPond's usual gap plus extra room\n"
            f"  % page header -> top system: usual (6 and 1) plus {PAGE_EXTRA_PT} pt\n"
            f"  top-system-spacing.basic-distance = #{g(6 * ss + PAGE_EXTRA_PT)}\n"
            f"  top-system-spacing.padding = #{g(1 * ss + PAGE_EXTRA_PT)}\n"
            f"  % bottom system -> footer: usual (1 and 1) plus {PAGE_EXTRA_PT} pt\n"
            f"  last-bottom-spacing.basic-distance = #{g(1 * ss + PAGE_EXTRA_PT)}\n"
            f"  last-bottom-spacing.padding = #{g(1 * ss + PAGE_EXTRA_PT)}\n"
            f"  % first page: LilyPond's usual gap under the titles (5 and 0.5) plus {FIRST_PAGE_EXTRA_PT} pt\n"
            f"  markup-system-spacing.basic-distance = #{g(5 * ss + FIRST_PAGE_EXTRA_PT)}\n"
            f"  markup-system-spacing.padding = #{g(0.5 * ss + FIRST_PAGE_EXTRA_PT)}\n"
            f"  % subtitle -> range line (\"I ii V I to ...\"): LilyPond's usual gap (1 and 0.5) plus {SUBTITLE_GAP_EXTRA_PT} pt\n"
            f"  markup-markup-spacing.basic-distance = #{g(1 * ss + SUBTITLE_GAP_EXTRA_PT)}\n"
            f"  markup-markup-spacing.padding = #{g(0.5 * ss + SUBTITLE_GAP_EXTRA_PT)}\n"
            "  % between systems: at least SYSTEM_GAP staff spaces of clear room between one\n"
            "  % line's Roman numerals and the next line's chord names (LilyPond's usual: 1)\n"
            "  % (the labels sit at fixed heights, so LilyPond doesn't see them: the distance from\n"
            "  % one staff to the next is set to hold both lines' labels plus the gap)\n"
            "  system-system-spacing.padding = #1\n"
            f"  system-system-spacing.minimum-distance = #{self.system_distance():.2f}\n"
            f"  system-system-spacing.basic-distance = #{self.system_distance() + 1:.2f}\n"
        )

    def subtitle_parts(self):
        """The subtitle: '4-chord permutations in C major of I ii IV V', then the frame
        and placement. Long chord lists are counted instead of listed."""
        key_text = tonic_label(self.key) + " " + MODES[self.mode_name][0].lower()
        parts = [(f'"{self.length}-chord permutations in"', len(f"{self.length}-chord permutations in")),
                 (mk_text(key_text), len(key_text))]
        if len(self.notes) <= SUBTITLE_LIST_MAX:
            parts.append(('"of"', 2))
            for k, t in enumerate(self.notes):
                mk = self.mk_chord(t)
                width = len(self.label(t) if self.labels != "both" else self.chords[t].roman_text()) + 1
                parts.append(((f'\\concat {{ {mk} "," }}' if k < len(self.notes) - 1 else mk), width))
        else:
            parts.append((f'"of {len(self.notes)} chords"', 3 + len(str(len(self.notes))) + 7))
        if self.frame_before and self.frame_after and self.frame_before == self.frame_after:
            parts.append((f'\\concat {{ {DASH}" framed by " {self.mk_chord(self.frame_before[0])} }}', 16))
        else:
            if self.frame_before:
                parts.append((f'\\concat {{ {DASH}" starting on " {self.mk_chord(self.frame_before[0])} }}', 17))
            if self.frame_after:
                parts.append((f'\\concat {{ {DASH}" ending on " {self.mk_chord(self.frame_after[0])} }}', 15))
        if self.voicing != "close" or self.double_bass:
            text = ({"drop2": "drop 2", "open": "open voicing"}.get(self.voicing, "")
                    + (", " if self.voicing != "close" and self.double_bass else "")
                    + ("bass doubled below" if self.double_bass else ""))
            parts.append((f'\\char ##x2013 "{text}"', 2 + len(text)))
        sfx = SUBTITLE_SUFFIX.get(self.placement, "")
        if sfx:
            parts.append((sfx, 2 + len(sfx.split('"')[1])))
        return parts

    def ly_file_header(self):
        """Everything at the top of a file, then the opening of its first \\score."""
        spacing = "#1/8" if self.lilypond == "2.26" else "#(ly:make-moment 1/8)"
        uniform_accidentals = (
            "    % an accidental on every note: every accidental gets the same slot\n"
            "    % (as wide as the widest sign in the music font), so all measures match\n"
            "    \\override Accidental.X-extent =\n"
            "      #(lambda (grob)\n"
            "         (let* ((font (ly:grob-default-font grob))\n"
            "                (widths (map (lambda (g)\n"
            "                               (interval-length (ly:stencil-extent (ly:font-get-glyph font g) X)))\n"
            "                             '(\"accidentals.sharp\" \"accidentals.flat\" \"accidentals.natural\"))))\n"
            "           (cons 0 (apply max widths))))\n"
            "    \\override Accidental.horizontal-skylines = #ly:grob::simple-horizontal-skylines-from-extents\n"
        ) if self.accidentals == "every" else ""
        return (
            f'\\version "{self.version}"\n'
            + (OUTLINE_SNIPPET.replace("@FONT@", self.music_font or "emmentaler")
               if self.outline_fonts else "")
            + f"#(set-global-staff-size {self.staff_size})\n"
            + {"off": "\\pointAndClickOff   % PDF without point-and-click links (smaller PDFs)\n",
               "notes": "\\pointAndClickOn\n\\pointAndClickTypes #'note-event   % PDF links on chords only:\n"
                        "% clicking a chord opens its line in this .ly file\n",
               "all": "\\pointAndClickOn   % PDF with point-and-click links on everything\n"}[self.pdf_links]
            + "\n"
            "% CC0 80x15 badge: vector EPS kept next to this file\n"
            f'ccZeroIcon = \\markup {{ \\epsfile #Y #{BADGE_HEIGHT} "{CC0_EPS_NAME}" }}\n'
            "% sharp / flat glyphs used in chord labels and titles (size and height adjustable)\n"
            "noteSharp = \\markup { \\raise #0.6 \\fontsize #-3 \\sharp }\n"
            "noteFlat = \\markup { \\raise #0.3 \\fontsize #-3 \\flat }\n"
            "noteDSharp = \\markup { \\raise #0.6 \\fontsize #-3 \\doublesharp }\n"
            "noteDFlat = \\markup { \\raise #0.3 \\fontsize #-3 \\doubleflat }\n"
            "% figured-bass inversion figures (6 over 4, 6 over 5 ...) after a Roman numeral\n"
            "#(define-markup-command (figureStack layout props figs) (markup-list?)\n"
            "   (interpret-markup layout props\n"
            "     (make-raise-markup 1.1 (make-fontsize-markup -3.5\n"
            "       (make-override-markup '(baseline-skip . 1.6) (make-column-markup figs))))))\n"
            "% centred multiplication-style cross standing for \"any chord\" in range labels,\n"
            "% drawn from two lines so it never depends on the text font (size and height adjustable)\n"
            "anyNote = \\markup {\n"
            "  \\raise #0.25\n"
            "  \\override #'(thickness . 1.4)\n"
            "  \\combine\n"
            "    \\draw-line #'(0.7 . 0.7)\n"
            "    \\raise #0.7 \\draw-line #'(0.7 . -0.7)\n"
            "}\n\n"
            "% where a line's chord names (above) and Roman numerals (below) sit, in staff spaces\n"
            "% from the middle line: set at the start of every line, just clear of that line's\n"
            "% own highest and lowest notes, so labels hug the music and line up across the line\n"
            "labelsAt = #(define-music-function (names numerals) (number? number?)\n"
            "  #{\n"
            "    \\override TextScript.Y-offset =\n"
            "      #(lambda (grob) (if (eqv? (ly:grob-property grob 'direction) UP) names numerals))\n"
            + (f"    \\override Score.RehearsalMark.Y-offset = #(+ names {MARK_ABOVE_NAMES})   % chunk labels\n"
               if self.labels != "roman" else "") +
            "  #})\n\n"
            + PERM_BAR_NUMBER
            + "\\paper {\n"
            "  paper-width = 8.5\\in\n"
            "  paper-height = 11\\in\n"
            f"  max-systems-per-page = {max(self.systems_per_page, self.first_page_systems)}\n"
            "  % page breaks are written into the music, so the quick, low-memory\n"
            "  % page layout is enough even for thousands of pages\n"
            "  page-breaking = #ly:minimal-breaking\n"
            "  indent = 0\\mm   % first line of music starts at the margin too\n"
            + self.spacing_block() +
            "  % the range line under the titles, centred on the page\n"
            "  scoreTitleMarkup = \\markup { \\fill-line { \\fromproperty #'header:piece } }\n"
            "  oddFooterMarkup = \\markup { \\fill-line { \\fromproperty #'header:copyright } }\n"
            "  evenFooterMarkup = \\markup { \\fill-line { \\fromproperty #'header:copyright } }\n"
            + self.fonts_block() +
            "}\n\n"
            "\\layout {\n"
            "  \\context {\n"
            "    \\Score\n"
            f"    proportionalNotationDuration = {spacing}\n"
            "    \\override SpacingSpanner.uniform-stretching = ##t\n"
            '    measureBarType = "."   % thick barline after every measure\n'
            "    barNumberVisibility = #all-bar-numbers-visible\n"
            "    \\override BarNumber.break-visibility = ##(#f #t #t)\n"
            "    % centred on its barline; a very wide number (a billion or more) at the start of a\n"
            "    % line begins at the margin instead, so it never hangs off the left edge\n"
            "    \\override BarNumber.self-alignment-X =\n"
            "      #(lambda (grob)\n"
            "         (let ((st (ly:grob-property grob 'stencil)))\n"
            "           (if (and (eqv? (ly:item-break-dir grob) RIGHT) (ly:stencil? st)\n"
            "                    (> (interval-length (ly:stencil-extent st X)) 8))\n"
            "               LEFT CENTER)))\n"
            "    \\override BarNumber.font-shape = #'italic\n"
            f"    \\override BarNumber.font-size = #{BAR_NUMBER_FONT_SIZE}   % 9 pt at staff size 20\n"
            "    % new lines only where the file says \\break, so every system\n"
            "    % holds exactly the same number of measures\n"
            "    \\override NonMusicalPaperColumn.line-break-permission = ##f\n"
            "    % measure number = the permutation's number (see permBarNumber above)\n"
            "    barNumberFormatter = #(permBarNumber 1)\n"
            + ("    % measure numbers stay by the barline, just above the staff, and the chunk labels\n"
               "    % sit above the chord names; both at fixed heights, so neither pushes the other\n"
               "    \\override BarNumber.outside-staff-priority = ##f\n"
               f"    \\override BarNumber.Y-offset = #{BARNUMBER_Y}\n"
               "    \\override RehearsalMark.outside-staff-priority = ##f\n"
               f"    \\override RehearsalMark.Y-offset = #{self.name_y + MARK_ABOVE_NAMES:.2f}\n"
               if self.labels != "roman" else "") +
            "  }\n"
            "  \\context {\n"
            "    \\Voice\n"
            "    \\omit Stem\n"
            + (f"    \\override NoteHead.duration-log = #{NOTEHEAD_LOG[self.noteheads]}   "
               f"% {NOTEHEADS[self.noteheads].lower()} heads; the chords are still quarter notes\n"
               if self.noteheads in NOTEHEAD_LOG else "") +
            "    % chord labels: names above the staff, Roman numerals below, centred on the chord\n"
            f"    \\override TextScript.font-size = #{LABEL_FONT_SIZE}\n"
            "    \\override TextScript.self-alignment-X = #CENTER\n"
            "    \\override TextScript.parent-alignment-X = #CENTER   % centred on the notehead, not its left edge\n"
            "    % names above, numerals below, each on one baseline across the line: every line\n"
            "    % sets its own heights with \\labelsAt (see above); this is the run's widest setting\n"
            "    \\override TextScript.outside-staff-priority = ##f\n"
            "    \\override TextScript.Y-offset =\n"
            f"      #(lambda (grob) (if (eqv? (ly:grob-property grob 'direction) UP) {self.name_y:.2f} {self.roman_y:.2f}))\n"
            "  }\n"
            "  \\context {\n"
            "    \\Staff\n"
            "    \\omit TimeSignature\n"
            + uniform_accidentals +
            "  }\n"
            "}\n\n"
            "\\header {\n"
            + "  title = \\markup " + self.fit_lines(
                [('"Chord Permutations"', 18)]
                + ([(TITLE_SUFFIX[self.mode], 2 + len(TITLE_SUFFIX[self.mode].split('"')[1]))]
                   if self.mode in TITLE_SUFFIX else []), TITLE_PT_PER_CHAR) + "\n"
            + "  subtitle = \\markup " + self.fit_lines(self.subtitle_parts(),
                                                        SUBTITLE_PT_PER_CHAR, SUBTITLE_LEADING) + "\n"
            "  copyright = \\markup \\fill-line {\n"
            "    \\line {\n"
            "      \\vcenter \\ccZeroIcon\n"
            "      \\hspace #1\n"
            f'      \\vcenter "{COPYRIGHT_TEXT}"\n'
            "      \\hspace #1\n"
            f'      \\vcenter \\with-url #"{CC0_DEED}" \\fontsize #-2 "{CC0_DEED[8:]}"\n'
            "    }\n"
            "  }\n"
            "  tagline = ##f\n"
            "}\n\n"
        )

    def book_open(self, start_page):
        """Start a \\book: one PDF. Its \\bookOutputName (the range it holds) is written
        into a reserved blank space once the book is finished.
        Returns (text, offset of that space within text)."""
        head = (f"% ---- one PDF: up to {self.pages_per_pdf:,} pages ----\n"
                "\\book {\n  ")
        text = (head + " " * self.book_room + "\n"
                f"  \\paper {{ first-page-number = {start_page} }}\n")
        return text, len(head)

    def book_name(self, first, last):
        return f'\\bookOutputName "{self.range_name(first, last)}"'.ljust(self.book_room)

    def ly_score_open(self, first_index):
        """Start a \\score block (the music is split into blocks of whole pages)."""
        key = (f"    \\key {self.key} \\{MODES[self.mode_name][2]}\n"
               "    \\accidentalStyle modern   % accidentals hold for the measure, then are cancelled\n"
               if self.accidentals == "key" else
               "    \\accidentalStyle dodecaphonic   % a natural, sharp or flat on every note\n")
        return (
            "\\score {\n"
            "  {  % absolute pitches: every chord is written out exactly\n"
            f"    \\clef {self.clef}\n"
            + key +
            f"    \\time {self.bar_chords}/4\n"
            # measure N = permutation N of the full set, also in ranged runs
            # LilyPond's own counter only reaches about 2.1 billion, so it counts 1, 2, 3 ...
            # within each block and permBarNumber adds the block's first permutation number
            f"    \\set Score.barNumberFormatter = #(permBarNumber {first_index + 1})\n"
            "    \\set Score.currentBarNumber = #1\n"
            '    \\bar ""\n'
        )

    def wrap(self, parts, pt_per_char):
        """Title-block text broken into lines that fit across the page, only between parts."""
        limit = TEXT_LINE_PT * 20 / self.staff_size / pt_per_char      # characters per line
        lines, cur, used = [], [], 0
        for markup, chars in parts:
            if cur and used + 1 + chars > limit:
                lines.append(cur)
                cur, used = [], 0
            cur.append(markup)
            used += chars + (1 if used else 0)
        lines.append(cur)
        return lines

    def fit_lines(self, parts, pt_per_char, leading=None):
        """Markup for title-block text: one centred line if it fits across the page,
        otherwise several centred lines, broken only between the given parts.
        parts: [(markup, width in characters)]; widths are estimates at staff size 20."""
        limit = TEXT_LINE_PT * 20 / self.staff_size / pt_per_char      # characters per line
        lines, cur, used = [], [], 0
        for markup, chars in parts:
            if cur and used + 1 + chars > limit:
                lines.append(cur)
                cur, used = [], 0
            if not cur and markup.startswith(DASH):
                markup = markup[len(DASH):]        # a suffix starting its own line needs no dash
            if not cur and markup.startswith("\\concat { " + DASH):
                markup = "\\concat { \"" + markup[len("\\concat { " + DASH) + 2:]
            cur.append(markup)
            used += chars + (1 if used else 0)
        lines.append(cur)
        if len(lines) == 1:
            return "\\line { " + " ".join(lines[0]) + " }"
        column = "\\center-column { " + " ".join("\\line { " + " ".join(l) + " }" for l in lines) + " }"
        if leading:   # distance between the lines' baselines, in staff spaces
            column = f"\\override #'(baseline-skip . {leading}) {column}"
        return column

    def piece_head(self, first):
        """The range line under the titles ("I ii V I to vi V IV I"), centred on the page.
        A long range goes on two centred lines: the first permutation and "to", then the last."""
        first_perm = self.mk_perm(self.tokens_at(first))
        width = (2 * self.length + 1) * PIECE_PT_PER_CHORD * self.staff_size / 20
        if width > TEXT_LINE_PT:
            return f'  \\header {{\n    piece = \\markup \\center-column {{ \\line {{ {first_perm} "to" }} '
        return f'  \\header {{\n    piece = \\markup \\line {{ {first_perm} "to" '

    def ly_score_close(self, first=None, last=None, placeholder=False):
        """End a \\score block. The first block of each file carries the file's
        range ("I ii V I to ..."); its end is filled in when the file is finished,
        so a placeholder of spaces is written if the end isn't known yet.
        Returns (text, offset of the placeholder within text or None)."""
        text, offset = "  }\n", None
        if first is not None:
            head = self.piece_head(first)
            if placeholder:
                offset = len(text) + len(head)
                text += head + " " * self.piece_room + " }\n  }\n"
            else:
                text += head + self.mk_perm(self.tokens_at(last)) + " }\n  }\n"
        return text + "}\n\n", offset

    def whole_file(self, first, last, first_page=1, out_name=None):
        """A complete score file holding permutations first..last in one book."""
        btext, boff = self.book_open(first_page)
        name = out_name or self.range_name(first, last)
        btext = (btext[:boff] + f'\\bookOutputName "{name}"'.ljust(self.book_room)
                 + btext[boff + self.book_room:])
        parts, n = [self.ly_file_header(), btext, self.ly_score_open(first)], 0
        for i in range(first, last + 1):
            parts.append(self.ly_line_start(i, n + 1))
            if i == first or i % self.chunk_size == 0:
                parts.append(self.ly_chunk_mark(i))
            n += 1
            parts.append(self.ly_bar(i, n))
        close, _ = self.ly_score_close(first, last)
        parts.append(self.ly_padding(n) + close + "}\n")
        return "".join(parts)

    def ly_chunk_mark(self, i):
        label = self.chunk_label(i)
        toks = self.tokens_at(i)[:self.depth] + ["x"] * (self.length - self.depth)
        # the score files are plain ASCII: ♭ ♯ ° ø in the comment become b # o h
        for a, b in (("♭", "b"), ("♯", "#"), ("°", "o"), ("ø", "h"), ("𝄪", "x"), ("𝄫", "bb")):
            label = label.replace(a, b)
        label = label.encode("ascii", "replace").decode("ascii")
        if not self.chunk_labels:
            return f'\n    % chunk: {label}\n'
        return f'\n    % chunk: {label}\n    \\mark \\markup \\small {self.mk_perm(toks)}\n'

    def chord_notes(self, tok, prev):
        """The chord's notes: root position, or (smooth voice leading) the voicing nearest
        the chord before it in the measure. Each measure starts afresh."""
        if self.placement != "nearest" or prev is None:
            key = (tok, None)
        else:
            key = (tok, prev)
        notes = self._voicing_cache.get(key)
        if notes is None:
            ch = self.chords[tok]
            notes = tuple(apply_voicing(ch.voicing(self.key, self.octave), self.voicing, ch.bass is not None)
                          if key[1] is None
                          else smooth_voicing(ch, self.key, self.octave, prev, self.voicing))
            if len(self._voicing_cache) < 200000:
                self._voicing_cache[key] = notes
        return notes

    def label_baselines(self):
        """Where the chord names and Roman numerals sit, in staff spaces from the middle
        line: one baseline each for the whole run, just past the highest and lowest note
        any measure of the run can reach (in any voicing the placement may pick)."""
        middle = CLEF_POS[self.clef]
        lo = hi = 0
        # every voicing a chord can actually get. A measure starts in root position, and
        # (smooth voice leading) each next chord follows from the one before it, so only
        # chains as long as a measure are possible: following them further would reach
        # voicings that drift far above or below anything a measure can hold.
        slots = ([[t] for t in self.frame_before] + [sorted(set(self.notes))] * self.length
                 + [[t] for t in self.frame_after])
        level = {self.chord_notes(t, None) for t in slots[0]}
        seen = set(level)
        for slot in slots[1:]:
            if self.placement != "nearest":
                level = {self.chord_notes(t, None) for t in slot}
            else:
                level = {self.chord_notes(t, prev) for prev in level for t in slot}
            seen |= level
        low_edge, high_edge = self.edges(seen)
        self.low_edge, self.high_edge = low_edge, high_edge
        return high_edge + LABEL_GAP_ABOVE, low_edge - LABEL_GAP_BELOW

    def edges(self, shapes):
        """(bottom of the lowest note, top of the highest) of these chord voicings, in staff
        spaces from the middle line; never inside the staff."""
        middle = CLEF_POS[self.clef]
        lo = hi = 0
        for shape in shapes:
            for pos, _ in shape:
                lo, hi = min(lo, pos - middle), max(hi, pos - middle)
            if self.double_bass:
                lo = min(lo, shape[0][0] - 7 - middle)
        return min(-2.0, lo / 2 - 0.5), max(2.0, hi / 2 + 1.0)   # room for a flat above

    def measure_notes(self, i):
        """The voicings of measure i's chords (frame chords included), in order."""
        notes = self._bar_notes.get(i)
        if notes is None:
            notes, prev = [], None
            for t in self.frame_before + self.tokens_at(i) + self.frame_after:
                prev = self.chord_notes(t, prev)
                notes.append(prev)
        return notes

    def labels_at(self, shapes):
        """Put this line's chord names and numerals just clear of its own highest and
        lowest notes: every line is aligned within itself, and hugs its own music."""
        low, high = self.edges(shapes)
        return f"\\labelsAt #{high + LABEL_GAP_ABOVE:.2f} #{low - LABEL_GAP_BELOW:.2f}"

    def ly_line_start(self, i, bar_in_book):
        """At the start of a line of music: where that line's labels sit."""
        if self.split_at:              # the line is the first half of measure i
            notes = self.measure_notes(i)
            self._bar_notes = {i: notes}
            return "    " + self.labels_at(notes[:self.split_at]) + "\n"
        if (bar_in_book - 1) % self.bars_per_system:
            return ""
        last = min(i + self.bars_per_system - 1, self.last)
        self._bar_notes = {j: self.measure_notes(j) for j in range(i, last + 1)}
        return "    " + self.labels_at([n for j in self._bar_notes for n in self._bar_notes[j]]) + "\n"

    def title_lines(self):
        """How many lines the title, the subtitle and the range line take on a PDF's first page."""
        title = [('"Chord Permutations"', 18)] + (
            [(TITLE_SUFFIX[self.mode], 2 + len(TITLE_SUFFIX[self.mode].split('"')[1]))]
            if self.mode in TITLE_SUFFIX else [])
        piece = (2 * self.length + 1) * PIECE_PT_PER_CHORD * self.staff_size / 20
        return (len(self.wrap(title, TITLE_PT_PER_CHAR)),
                len(self.wrap(self.subtitle_parts(), SUBTITLE_PT_PER_CHAR)),
                2 if piece > TEXT_LINE_PT else 1)

    def systems_that_fit(self, first_page):
        """How many systems fit on a page, from the distance between systems (which holds
        both lines' labels): measured with LilyPond on letter paper at several staff sizes."""
        ss = self.staff_size / 4.0                      # one staff space, in points
        room = PAGE_SYSTEM_ROOM_PT / ss                 # in staff spaces
        if first_page:
            t, sub, piece = self.title_lines()
            room -= (TITLE_BLOCK_SS + TITLE_LINE_SS * (t - 1) + SUBTITLE_LINE_SS * (sub - 1)
                     + PIECE_LINE_SS * (piece - 1)
                     + (NAMES_UNDER_TITLE_SS if self.labels != "roman" else 0))
        n = int((room + SYSTEM_GAP) / (self.system_distance() + FIT_SAFETY_SS))
        if self.split_at:                               # two lines per measure: whole measures only
            n -= n % 2
            return max(2, n)
        return max(1, n)

    def system_distance(self):
        """Middle line to middle line of two systems, in staff spaces: this line's lowest
        label (or note), the next line's highest, and SYSTEM_GAP of clear room between."""
        below = max(-self.roman_y + 0.7 if self.labels != "names" else 0.0, -self.low_edge, 2.0)
        above = max(self.name_y + 1.9 if self.labels != "roman" else 0.0, self.high_edge, 2.0,
                    self.name_y + MARK_ABOVE_NAMES + 1.6
                    if self.labels != "roman" and self.chunk_labels else 0.0)   # chunk label
        return below + above + SYSTEM_GAP

    def chord_labels(self, tok):
        """The chord's labels as LilyPond text: names above (^), Roman numerals below (_)."""
        text = self._label_cache.get(tok)
        if text is None:
            ch = self.chords[tok]
            text = ""
            if self.labels in ("names", "both"):
                text += "^\\markup " + name_markup(ch, self.key)
            if self.labels in ("roman", "both"):
                text += "_\\markup " + roman_markup(ch)
            self._label_cache[tok] = text
        return text

    def ly_bar(self, i, bar_in_book):
        toks = self.frame_before + self.tokens_at(i) + self.frame_after
        voicings = self.measure_notes(i)
        words = []
        for k, (t, notes) in enumerate(zip(toks, voicings)):
            out = ((notes[0][0] - 7, notes[0][1] - 12),) + notes if self.double_bass else notes
            words.append("<" + " ".join(ly_pitch(*n) for n in out) + ">"
                         + (NOTE_LENGTH if k == 0 else "") + self.chord_labels(t))
        if self.split_at:
            words.insert(self.split_at, '\\bar "" \\break '      # split line, no barline
                         + self.labels_at(voicings[self.split_at:]))
        line = "    " + " ".join(words) + " |"
        if self.page_ends_after(bar_in_book):
            line += " \\pageBreak"        # a full page: new page (and new line)
        elif bar_in_book % self.bars_per_system == 0:
            line += " \\break"
        return line + "\n"

    def ly_padding(self, bars_in_file):
        """If the last line of music is short, finish it with invisible measures so
        its real measures are exactly as wide as on every other line."""
        missing = -bars_in_file % self.bars_per_system
        if not missing:
            return ""
        p = CLEF_MIDDLE[self.clef]
        lines = ["",
                 "    % invisible measures: keep the last line's measures the same width. They are",
                 "    % hidden (not removed), so their barlines and numbers still take up their usual",
                 "    % room and every measure on this line is spaced exactly like the full lines",
                 "    % (the staff carries on with invisible lines: with no staff at all the",
                 "    % hidden barlines would have no width and the real measures would stretch)",
                 "    \\stopStaff",
                 "    \\override Staff.StaffSymbol.transparent = ##t",
                 "    \\startStaff",
                 "    \\hideNotes \\hide Score.BarNumber"]
        for k in range(missing):
            notes = [p + NOTE_LENGTH] + [p] * (self.bar_chords - 1)
            if k == 0:
                notes.insert(1, "\\hide Staff.BarLine")
            lines.append("    \\absolute { " + " ".join(notes) + " } |")
        return "\n".join(lines) + "\n"

    def write_master(self, files):
        """master.ly: pulls every finished file of this run into one PDF."""
        lines = [
            f'\\version "{self.version}"',
            "% Engraves every file of this run in ONE LilyPond run (the PDFs are split",
            "% into books of the chosen page count). Fine for small runs; for large",
            "% runs use engrave_all.bat (Windows) or engrave_all.command (Mac), which",
            "% engrave one file at a time so LilyPond's memory never fills up.",
            "% Engrave with:  lilypond master.ly   (run it inside this folder,",
            f"% so {CC0_EPS_NAME} - the footer icon - is found)",
            "",
        ] + [f'\\include "{name}"' for name in files]
        tmp = os.path.join(self.out_dir, "master.ly.tmp")
        with open(tmp, "w") as f:
            f.write("\n".join(lines) + "\n")
        replace_file(tmp, os.path.join(self.out_dir, "master.ly"))



ENGRAVE_BAT = r"""@echo off
setlocal
rem ---------------------------------------------------------------------------
rem  Engraves every score file in this folder, ONE LilyPond run per file, so
rem  LilyPond only ever holds one file in memory. Each file makes its own PDFs
rem  (split by the app into books of the chosen page count). Double-click to run.
rem
rem  If LilyPond is not found, put the full path to lilypond.exe here, e.g.
rem    set "LILYPOND=C:\Program Files\lilypond-2.26.0\bin\lilypond.exe"
rem ---------------------------------------------------------------------------
set "LILYPOND=lilypond"
cd /d "%~dp0"

where "%LILYPOND%" >nul 2>nul
if errorlevel 1 (
  for /d %%D in ("%ProgramFiles%\lilypond-*" "%ProgramFiles(x86)%\lilypond-*" "%USERPROFILE%\lilypond-*") do (
    if exist "%%~D\bin\lilypond.exe" set "LILYPOND=%%~D\bin\lilypond.exe"
  )
)

set /a DONE=0, FAILED=0
for %%F in (*.ly) do call :engrave "%%~F"
echo.
echo Finished: %DONE% file(s) engraved, %FAILED% with errors.
pause
exit /b

:engrave
if /i "%~1"=="master.ly" exit /b
if /i "%~1"=="_in_progress.ly" exit /b
echo.
echo === Engraving %~1 ...
"%LILYPOND%" "%~1"
if errorlevel 1 (set /a FAILED+=1) else (set /a DONE+=1)
exit /b
"""

ENGRAVE_COMMAND = r"""#!/bin/bash
# ---------------------------------------------------------------------------
#  Engraves every score file in this folder, ONE LilyPond run per file, so
#  LilyPond only ever holds one file in memory. Each file makes its own PDFs
#  (split by the app into books of the chosen page count). Double-click to run.
#
#  If LilyPond is not found, put its full path here, for example:
#    LILYPOND="$HOME/lilypond-2.26.0/bin/lilypond"
#    LILYPOND="/opt/homebrew/bin/lilypond"
# ---------------------------------------------------------------------------
LILYPOND="lilypond"
export PATH="/opt/homebrew/bin:/usr/local/bin:$HOME/bin:$PATH"
cd "$(dirname "$0")" || exit 1

if ! command -v "$LILYPOND" >/dev/null 2>&1; then
  for c in "$HOME"/lilypond-*/bin/lilypond /Applications/lilypond-*/bin/lilypond \
           /Applications/LilyPond*.app/Contents/Resources/bin/lilypond; do
    [ -x "$c" ] && LILYPOND="$c"
  done
fi

done_n=0; failed=0
for f in *.ly; do
  case "$f" in master.ly|_in_progress.ly) continue ;; esac
  [ -e "$f" ] || continue
  echo
  echo "=== Engraving $f ..."
  if "$LILYPOND" "$f"; then done_n=$((done_n+1)); else failed=$((failed+1)); fi
done
echo
echo "Finished: $done_n file(s) engraved, $failed with errors."
read -r -p "Press Return to close."
"""


def write_engrave_scripts(folder, lilypond=None):
    """engrave_all.bat (Windows) and engrave_all.command (Mac) in a run folder,
    set to use the LilyPond this app found (they still search if it's gone)."""
    bat, cmd = ENGRAVE_BAT, ENGRAVE_COMMAND
    if lilypond and '"' not in lilypond:
        bat = bat.replace('set "LILYPOND=lilypond"', f'set "LILYPOND={lilypond}"')
        cmd = cmd.replace('LILYPOND="lilypond"', f'LILYPOND="{lilypond}"')
    with open(os.path.join(folder, "engrave_all.bat"), "w", newline="\r\n") as f:
        f.write(bat)
    path = os.path.join(folder, "engrave_all.command")
    with open(path, "w", newline="\n") as f:
        f.write(cmd)
    try:
        os.chmod(path, 0o755)   # double-clickable on a Mac
    except OSError:
        pass


def fresh_state(settings):
    return {
        "version": STATE_VERSION,
        "settings": settings,
        "next_index": Plan(settings).first,   # next permutation to write
        "file_first": None,  # name of the first permutation in the current file
        "file_start": None,  # index of the first permutation in the current file
        "file_count": 0,     # bars written to the current file
        "file_bytes": 0,     # bytes written to the current file
        "score_index": 0,    # which \score block of the current file is open
        "score_bars": 0,     # measures in that block so far
        "piece_at": None,    # where the file's range line is filled in at the end
        "book_first": None,  # first permutation in the current \\book (PDF)
        "book_bars": 0,      # measures in that book so far
        "book_name_at": None,  # where its \\bookOutputName is filled in
        "pages_done": 0,     # pages in finished files (page numbers carry on)
        "elapsed": 0.0,      # running time across all runs (pauses excluded)
        "done": False,
        "files": [],         # finished files
    }


class Engine:
    """Does the generating on a background thread; the web page controls it."""

    def __init__(self):
        self.lock = threading.Lock()
        self.wake = threading.Condition(self.lock)
        self.thread = None
        self.paused = False
        self.stop_requested = False
        self.status = "idle"   # idle | running | paused | stopped | done | error
        self.message = "Choose your settings, then press Start."
        self.recent = []       # last few bars written, for the preview
        self.state = self._load()
        self.plan = Plan(self.state["settings"])

    # ---------- persistence ----------
    def _load(self):
        if not os.path.exists(STATE_FILE):
            return fresh_state(dict(DEFAULT_SETTINGS))
        try:
            with open(STATE_FILE) as f:
                st = json.load(f)
        except (OSError, ValueError):
            st = {}
        if st.get("version") != STATE_VERSION:
            self.message = (f"Found a {STATE_FILE} from an earlier version; "
                            "it will be replaced when you press Start.")
            return fresh_state(dict(DEFAULT_SETTINGS))
        if st["done"]:
            self.status = "done"
            self.message = f"Last run finished: {len(st['files'])} file(s)."
        elif st["next_index"] > 0:
            self.status = "stopped"
            self.message = (f"Ready to resume at "
                            f"{Plan(st['settings']).line_at(st['next_index'])}.")
        return st

    def _save(self):
        if getattr(self, "_txt", None):
            self._txt.flush()   # never record more text than is really on disk
        tmp = STATE_FILE + ".tmp"
        with open(tmp, "w") as f:
            json.dump(self.state, f, indent=2)
        replace_file(tmp, STATE_FILE)  # atomic: the memory file is never half-written

    def _finish_file(self):
        st, plan = self.state, self.plan
        last = st["next_index"] - 1
        first_block = st["score_index"] == 0 and st.get("piece_at") is None
        close, _ = plan.ly_score_close(st["file_start"] if first_block else None, last)
        with open(plan.working, "ab") as f:
            f.write((plan.ly_padding(st["file_count"]) + close
                     + "}\n").encode("ascii"))   # end of the file's last \\book
        if st.get("piece_at") is not None:
            # fill in the end of the range line in the file's first \score block
            end = (plan.mk_perm(plan.tokens_at(last))).ljust(plan.piece_room)
            with open(plan.working, "r+b") as f:
                f.seek(st["piece_at"])
                f.write(end.encode("ascii"))
        if st.get("book_name_at") is not None:
            self._fill(plan.working, st["book_name_at"],
                       plan.book_name(st["book_first"], last))
            self._index_row(st["book_first"], last, st.get("book_page", 1))
        st["pages_done"] = st.get("pages_done", 0) + plan.file_pages(st["file_count"])
        name = (plan.range_name(st["file_start"], last) if st.get("file_start") is not None
                else f"{st['file_first']}-{plan.name_at(last)}") + ".ly"
        replace_file(plan.working, os.path.join(plan.out_dir, name))
        st["files"].append(name)
        st.update(file_first=None, file_start=None, file_count=0, file_bytes=0,
                  score_index=0, score_bars=0, piece_at=None,
                  book_first=None, book_bars=0, book_name_at=None)
        plan.write_master(st["files"])
        self._save()

    def _index_row(self, first, last, first_page):
        """Add one PDF to index.csv: its name, range, measures and pages."""
        st, plan = self.state, self.plan
        rows = ""
        if not st.get("index_bytes"):
            rows = "pdf,first permutation,last permutation,first measure,last measure,first page,last page\n"
        pages = plan.book_pages(last - first + 1)
        rows += (f"{plan.range_name(first, last)}.pdf,{plan.line_at(first)},"
                 f"{plan.line_at(last)},{first + 1},{last + 1},{first_page},{first_page + pages - 1}\n")
        data = rows.encode("utf-8")
        with open(plan.index_path, "ab") as f:
            f.write(data)
        st["index_bytes"] = st.get("index_bytes", 0) + len(data)

    @staticmethod
    def _fill(path, offset, text):
        """Write text over a reserved blank space earlier in a file."""
        with open(path, "r+b") as f:
            f.seek(offset)
            f.write(text.encode("ascii"))

    # ---------- controls ----------
    def start(self, raw_settings=None):
        with self.lock:
            if self.status == "running":
                return
            if self.status == "paused":
                self.paused = False
                self.status, self.message = "running", ""
                self.wake.notify_all()
                return
            if self.status != "stopped":
                # Fresh run with the panel's settings.
                settings, err = validate(raw_settings or {})
                if err:
                    self.message = err
                    return
                settings["folder_name"] = Plan(settings).folder_name(settings)   # new-style name
                plan = Plan(settings)
                if plan.name_tail < 1:
                    widest = max(len(n) for n in plan.notes)
                    need = len(os.path.abspath(plan.out_dir)) + 1 + plan.length * widest + 2 * widest + 5
                    self.message = (f"Even shortened, file paths would be about {need} characters, past "
                                    "Windows' 260 limit. Choose a save folder with a shorter "
                                    "path (e.g. C:\\Perm).")
                    return
                settings["name_tail"] = plan.name_tail      # resume with the same names
                self.state = fresh_state(settings)
                self.plan = plan
                self.recent = []
            self.paused = self.stop_requested = False
            self.status, self.message = "running", (self.plan.fit_note if self.plan else "")
            self.thread = threading.Thread(target=self._run, daemon=True)
            self.thread.start()

    def pause(self):
        with self.lock:
            if self.status == "running":
                self.paused = True
                self.status, self.message = "paused", "Paused. Press Start to continue."

    def stop(self):
        with self.lock:
            if self.status not in ("running", "paused"):
                return
            self.stop_requested = True
            self.paused = False
            self.wake.notify_all()
            thread = self.thread
        if thread:
            thread.join()

    def reset(self):
        with self.lock:
            if self.status in ("running", "paused"):
                self.message = "Stop first, then Reset."
                return
            for path in (STATE_FILE, self.plan.working):
                if os.path.exists(path):
                    os.remove(path)
            self.state = fresh_state(self.state["settings"])
            self.recent = []
            self.status, self.message = "idle", "Reset. Choose your settings, then press Start."

    def snapshot(self):
        with self.lock:
            st, plan = self.state, self.plan
            i = min(st["next_index"], plan.last + 1)
            done = i - plan.first
            return {
                "status": self.status,
                "message": self.message,
                "locked": self.status in ("running", "paused", "stopped"),
                "settings": st["settings"],
                "tonics": {t: tonic_label(t) for t in TONICS},
                "modes": {k: v[0] for k, v in MODES.items()},
                "sizes": {k: v[0] for k, v in SIZES.items()},
                "extras": {k: list(v) for k, v in EXTRAS.items()},
                "qualities": {k: v[0] for k, v in QUALITIES.items()},
                "labels": LABELS,
                "noteheads": NOTEHEADS,
                "voicings": VOICINGS,
                "accidentals": ACCIDENTALS,
                "repeat_modes": REPEAT_MODES,
                "script_dir": DATA_DIR,
                "default_place": DEFAULT_PLACE,
                "app_name": APP_NAME,
                "windowed": WINDOW is not None, "window_note": WINDOW_NOTE,
                "clefs": CLEFS,
                "pitches": PITCHES,
                "placements": PLACEMENTS,
                "pdf_links": PDF_LINKS,
                "limits": {"min_len": MIN_LEN, "max_len": MAX_LEN,
                           "min_kb": MIN_KB, "max_kb": MAX_KB,
                           "min_staff": MIN_STAFF, "max_staff": MAX_STAFF,
                           "min_systems": MIN_SYSTEMS, "max_systems": MAX_SYSTEMS},
                "music_font_warning": MUSIC_FONT_WARNING,
                "outline_warning": OUTLINE_WARNING,
                "outline_required": sorted(OUTLINE_REQUIRED),
                "lilypond": _lp_info,
                "engrave": engraver.snapshot(),
                "lilypond_versions": LILYPOND_VERSIONS,
                "done_count": done,
                "total": plan.count,
                "done_text": f"{done:,}",
                "total_text": f"{plan.count:,}",
                "percent": 100 * done / plan.count,
                "elapsed": st["elapsed"],
                "chunk": plan.chunk_label(i),
                "out_dir": plan.out_dir,
                "current_file": (f"{st['file_first']}-…" if st["file_first"] else None),
                "files": st["files"][-50:],
                "file_total": len(st["files"]),
                "recent": self.recent,
            }

    # ---------- the work ----------
    def _run(self):
        try:
            self._work()
        except Exception as e:  # show problems in the panel instead of dying silently
            with self.lock:
                self._close_txt()
                self.status, self.message = "error", f"Error: {e}"
                # keep what's done: the run is stopped at the place reached (everything before
                # it is safely written), so Resume carries on from it
                if not self.state.get("done") and self.state["next_index"] > self.plan.first:
                    at = self.plan.line_at(self.state["next_index"])
                    self.status = "stopped"
                    try:
                        self._save()
                        self.message = (f"Stopped by an error: {e}  Progress is saved: press Resume "
                                        f"to carry on at {at}.")
                    except Exception:
                        self.message = (f"Stopped by an error: {e}  The progress file couldn't be saved "
                                        f"either, so press Resume now (before quitting) to carry on at {at}.")

    def _work(self):
        st, plan = self.state, self.plan
        os.makedirs(plan.out_dir, exist_ok=True)
        with open(os.path.join(plan.out_dir, CC0_EPS_NAME), "w") as f:
            f.write(CC0_EPS)   # the footer icon the scores refer to
        write_engrave_scripts(plan.out_dir, find_lilypond().get("path"))
        with self.lock:
            # Cut the working file back to the last saved point so nothing
            # written after the last save gets duplicated.
            if os.path.exists(plan.working):
                with open(plan.working, "r+b") as f:
                    f.truncate(st["file_bytes"])
            elif st["file_count"] > 0:
                st.update(file_first=None, file_start=None, file_count=0, file_bytes=0,
                          score_index=0, score_bars=0, piece_at=None,
                  book_first=None, book_bars=0, book_name_at=None)
            # index.csv: cut back to the last saved point too
            st.setdefault("index_bytes", 0)
            if os.path.exists(plan.index_path):
                with open(plan.index_path, "r+b") as f:
                    f.truncate(st["index_bytes"])
            for key, default in (("txt_bytes", 0), ("txt_first", None), ("txt_files", [])):
                st.setdefault(key, default)
            self._txt = None
            if plan.write_txt:
                if os.path.exists(plan.txt_working):
                    with open(plan.txt_working, "r+b") as f:
                        f.truncate(st["txt_bytes"])
                elif st["txt_bytes"] > 0:
                    st.update(txt_first=None, txt_bytes=0)   # it was already renamed
                self._txt = open(plan.txt_working, "ab")
            self._save()
        out = open(plan.working, "ab")
        last_tick = last_save = time.time()

        while True:
            with self.lock:
                if self.paused:
                    out.flush()
                    self._save()
                    while self.paused and not self.stop_requested:
                        self.wake.wait()
                    last_tick = time.time()  # paused time doesn't count
                if self.stop_requested:
                    out.flush()
                    out.close()
                    self._save()
                    self._close_txt()
                    self.status = "stopped"
                    self.message = (f"Stopped and saved. Press Start to resume at "
                                    f"{plan.line_at(st['next_index'])}.")
                    return
                if st["next_index"] > plan.last:
                    break

                i = st["next_index"]
                new_file = st["file_first"] is None
                new_block, piece_rel, book_rel, fill_book = new_file, None, None, None
                if new_file:
                    text = plan.ly_file_header()
                    book_page = st.get("pages_done", 0) + 1
                    btext, boff = plan.book_open(book_page)
                    book_rel = len(text) + boff
                    text += btext + plan.ly_score_open(i)
                elif st["score_bars"] >= (plan.first_score_measures
                                          if st["score_bars"] == st.get("book_bars", 0)
                                          else plan.score_measures):
                    # (a book's first block holds its first page, so its size differs)
                    # close this \score block (whole pages) and open the next one
                    first_block = st["score_index"] == 0
                    text, piece_rel = plan.ly_score_close(
                        st["file_start"] if first_block else None, placeholder=first_block)
                    if st["book_bars"] >= plan.book_measures:
                        # the book (PDF) is full: close it and start the next one
                        text += "}\n\n"
                        fill_book = (st["book_name_at"], st["book_first"], i - 1)
                        book_page = (st.get("pages_done", 0)
                                     + plan.file_pages(st["file_count"]) + 1)
                        btext, boff = plan.book_open(book_page)
                        book_rel = len(text) + boff
                        text += btext
                    text += plan.ly_score_open(i)
                    new_block = True
                else:
                    text = ""
                bar_in_book = 1 if book_rel is not None else st.get("book_bars", 0) + 1
                text += plan.ly_line_start(i, bar_in_book)     # this line's label heights
                if new_block or i % plan.chunk_size == 0:
                    text += plan.ly_chunk_mark(i)
                text += plan.ly_bar(i, bar_in_book)
                data = text.encode("ascii")

                if not new_file and (st["file_bytes"] + len(data) + FOOTER_RESERVE
                                     + plan.piece_room > plan.max_bytes or plan.tail_boundary(i)):
                    out.close()
                    self._finish_file()
                    out = open(plan.working, "ab")
                    continue  # rebuild this bar with the new file's header

                if new_file:
                    st["file_first"] = plan.name_at(i)
                    st["file_start"] = i
                if piece_rel is not None:
                    st["piece_at"] = st["file_bytes"] + piece_rel
                if fill_book:
                    out.flush()
                    self._fill(plan.working, fill_book[0],
                               plan.book_name(fill_book[1], fill_book[2]))
                    self._index_row(fill_book[1], fill_book[2], st.get("book_page", 1))
                if book_rel is not None:
                    st["book_name_at"] = st["file_bytes"] + book_rel
                    st["book_first"] = i
                    st["book_bars"] = 0
                    st["book_page"] = book_page
                st["book_bars"] = st.get("book_bars", 0) + 1
                if new_block:
                    st["score_index"] = 0 if new_file else st["score_index"] + 1
                    st["score_bars"] = 0
                st["score_bars"] += 1
                out.write(data)
                if self._txt:
                    line = (plan.line_at(i) + "\n").encode("utf-8")
                    if st["txt_bytes"] > 0 and (st["txt_bytes"] + len(line) > plan.max_bytes
                                                or plan.tail_boundary(i)):
                        self._finish_txt(i - 1)
                    if st["txt_first"] is None:
                        st["txt_first"] = plan.name_at(i)
                        st["txt_start"] = i
                    self._txt.write(line)
                    st["txt_bytes"] += len(line)
                st["file_bytes"] += len(data)
                st["file_count"] += 1
                st["next_index"] += 1
                self.recent = (self.recent + [plan.line_at(i)])[-8:]

                now = time.time()
                st["elapsed"] += now - last_tick
                last_tick = now
                if now - last_save > 1.0:
                    out.flush()
                    self._save()
                    last_save = now

            time.sleep(ROW_DELAY)  # 0 still lets the panel get a word in

        with self.lock:
            out.close()
            if st["file_count"] > 0:
                self._finish_file()
            if self._txt and st["txt_bytes"] > 0:
                self._finish_txt(plan.last, reopen=False)
            st["done"] = True
            self._save()
            self._close_txt()
            if os.path.exists(plan.txt_working):
                os.remove(plan.txt_working)   # nothing left in it
            self.status = "done"
            nt = len(st.get("txt_files", []))
            extra = f" and {nt} text file(s)" if plan.write_txt else ""
            self.message = (f"Finished. {len(st['files'])} score file(s){extra} written to "
                            f"'{plan.out_dir}'." + (" " + plan.fit_note if plan.fit_note else ""))

    def _finish_txt(self, last, reopen=True):
        """Close the current text list, name it first-last.txt, start a new one."""
        st, plan = self.state, self.plan
        self._txt.close()
        name = (plan.range_name(st["txt_start"], last) if st.get("txt_start") is not None
                else f"{st['txt_first']}-{plan.name_at(last)}") + ".txt"
        replace_file(plan.txt_working, os.path.join(plan.out_dir, name))
        st["txt_files"].append(name)
        st.update(txt_first=None, txt_start=None, txt_bytes=0)
        self._txt = open(plan.txt_working, "ab") if reopen else None
        self._save()

    def _close_txt(self):
        if getattr(self, "_txt", None):
            self._txt.close()
        self._txt = None


# ---------------- control panel ----------------
# ---------------- Harmonarium's own license ----------------
APP_COPYRIGHT = "Copyright (C) 2026 Joshua Nichols"
APP_SOURCE_URL = "https://github.com/joshdnichols/Harmonarium"
APP_LICENSE_SPDX = "GPL-3.0-or-later"
# the full GNU General Public License, version 3 (served at /license/gpl)
GPL3_TEXT = """                    GNU GENERAL PUBLIC LICENSE
                       Version 3, 29 June 2007

 Copyright (C) 2007 Free Software Foundation, Inc. <https://fsf.org/>
 Everyone is permitted to copy and distribute verbatim copies
 of this license document, but changing it is not allowed.

                            Preamble

  The GNU General Public License is a free, copyleft license for
software and other kinds of works.

  The licenses for most software and other practical works are designed
to take away your freedom to share and change the works.  By contrast,
the GNU General Public License is intended to guarantee your freedom to
share and change all versions of a program--to make sure it remains free
software for all its users.  We, the Free Software Foundation, use the
GNU General Public License for most of our software; it applies also to
any other work released this way by its authors.  You can apply it to
your programs, too.

  When we speak of free software, we are referring to freedom, not
price.  Our General Public Licenses are designed to make sure that you
have the freedom to distribute copies of free software (and charge for
them if you wish), that you receive source code or can get it if you
want it, that you can change the software or use pieces of it in new
free programs, and that you know you can do these things.

  To protect your rights, we need to prevent others from denying you
these rights or asking you to surrender the rights.  Therefore, you have
certain responsibilities if you distribute copies of the software, or if
you modify it: responsibilities to respect the freedom of others.

  For example, if you distribute copies of such a program, whether
gratis or for a fee, you must pass on to the recipients the same
freedoms that you received.  You must make sure that they, too, receive
or can get the source code.  And you must show them these terms so they
know their rights.

  Developers that use the GNU GPL protect your rights with two steps:
(1) assert copyright on the software, and (2) offer you this License
giving you legal permission to copy, distribute and/or modify it.

  For the developers' and authors' protection, the GPL clearly explains
that there is no warranty for this free software.  For both users' and
authors' sake, the GPL requires that modified versions be marked as
changed, so that their problems will not be attributed erroneously to
authors of previous versions.

  Some devices are designed to deny users access to install or run
modified versions of the software inside them, although the manufacturer
can do so.  This is fundamentally incompatible with the aim of
protecting users' freedom to change the software.  The systematic
pattern of such abuse occurs in the area of products for individuals to
use, which is precisely where it is most unacceptable.  Therefore, we
have designed this version of the GPL to prohibit the practice for those
products.  If such problems arise substantially in other domains, we
stand ready to extend this provision to those domains in future versions
of the GPL, as needed to protect the freedom of users.

  Finally, every program is threatened constantly by software patents.
States should not allow patents to restrict development and use of
software on general-purpose computers, but in those that do, we wish to
avoid the special danger that patents applied to a free program could
make it effectively proprietary.  To prevent this, the GPL assures that
patents cannot be used to render the program non-free.

  The precise terms and conditions for copying, distribution and
modification follow.

                       TERMS AND CONDITIONS

  0. Definitions.

  "This License" refers to version 3 of the GNU General Public License.

  "Copyright" also means copyright-like laws that apply to other kinds of
works, such as semiconductor masks.

  "The Program" refers to any copyrightable work licensed under this
License.  Each licensee is addressed as "you".  "Licensees" and
"recipients" may be individuals or organizations.

  To "modify" a work means to copy from or adapt all or part of the work
in a fashion requiring copyright permission, other than the making of an
exact copy.  The resulting work is called a "modified version" of the
earlier work or a work "based on" the earlier work.

  A "covered work" means either the unmodified Program or a work based
on the Program.

  To "propagate" a work means to do anything with it that, without
permission, would make you directly or secondarily liable for
infringement under applicable copyright law, except executing it on a
computer or modifying a private copy.  Propagation includes copying,
distribution (with or without modification), making available to the
public, and in some countries other activities as well.

  To "convey" a work means any kind of propagation that enables other
parties to make or receive copies.  Mere interaction with a user through
a computer network, with no transfer of a copy, is not conveying.

  An interactive user interface displays "Appropriate Legal Notices"
to the extent that it includes a convenient and prominently visible
feature that (1) displays an appropriate copyright notice, and (2)
tells the user that there is no warranty for the work (except to the
extent that warranties are provided), that licensees may convey the
work under this License, and how to view a copy of this License.  If
the interface presents a list of user commands or options, such as a
menu, a prominent item in the list meets this criterion.

  1. Source Code.

  The "source code" for a work means the preferred form of the work
for making modifications to it.  "Object code" means any non-source
form of a work.

  A "Standard Interface" means an interface that either is an official
standard defined by a recognized standards body, or, in the case of
interfaces specified for a particular programming language, one that
is widely used among developers working in that language.

  The "System Libraries" of an executable work include anything, other
than the work as a whole, that (a) is included in the normal form of
packaging a Major Component, but which is not part of that Major
Component, and (b) serves only to enable use of the work with that
Major Component, or to implement a Standard Interface for which an
implementation is available to the public in source code form.  A
"Major Component", in this context, means a major essential component
(kernel, window system, and so on) of the specific operating system
(if any) on which the executable work runs, or a compiler used to
produce the work, or an object code interpreter used to run it.

  The "Corresponding Source" for a work in object code form means all
the source code needed to generate, install, and (for an executable
work) run the object code and to modify the work, including scripts to
control those activities.  However, it does not include the work's
System Libraries, or general-purpose tools or generally available free
programs which are used unmodified in performing those activities but
which are not part of the work.  For example, Corresponding Source
includes interface definition files associated with source files for
the work, and the source code for shared libraries and dynamically
linked subprograms that the work is specifically designed to require,
such as by intimate data communication or control flow between those
subprograms and other parts of the work.

  The Corresponding Source need not include anything that users
can regenerate automatically from other parts of the Corresponding
Source.

  The Corresponding Source for a work in source code form is that
same work.

  2. Basic Permissions.

  All rights granted under this License are granted for the term of
copyright on the Program, and are irrevocable provided the stated
conditions are met.  This License explicitly affirms your unlimited
permission to run the unmodified Program.  The output from running a
covered work is covered by this License only if the output, given its
content, constitutes a covered work.  This License acknowledges your
rights of fair use or other equivalent, as provided by copyright law.

  You may make, run and propagate covered works that you do not
convey, without conditions so long as your license otherwise remains
in force.  You may convey covered works to others for the sole purpose
of having them make modifications exclusively for you, or provide you
with facilities for running those works, provided that you comply with
the terms of this License in conveying all material for which you do
not control copyright.  Those thus making or running the covered works
for you must do so exclusively on your behalf, under your direction
and control, on terms that prohibit them from making any copies of
your copyrighted material outside their relationship with you.

  Conveying under any other circumstances is permitted solely under
the conditions stated below.  Sublicensing is not allowed; section 10
makes it unnecessary.

  3. Protecting Users' Legal Rights From Anti-Circumvention Law.

  No covered work shall be deemed part of an effective technological
measure under any applicable law fulfilling obligations under article
11 of the WIPO copyright treaty adopted on 20 December 1996, or
similar laws prohibiting or restricting circumvention of such
measures.

  When you convey a covered work, you waive any legal power to forbid
circumvention of technological measures to the extent such circumvention
is effected by exercising rights under this License with respect to
the covered work, and you disclaim any intention to limit operation or
modification of the work as a means of enforcing, against the work's
users, your or third parties' legal rights to forbid circumvention of
technological measures.

  4. Conveying Verbatim Copies.

  You may convey verbatim copies of the Program's source code as you
receive it, in any medium, provided that you conspicuously and
appropriately publish on each copy an appropriate copyright notice;
keep intact all notices stating that this License and any
non-permissive terms added in accord with section 7 apply to the code;
keep intact all notices of the absence of any warranty; and give all
recipients a copy of this License along with the Program.

  You may charge any price or no price for each copy that you convey,
and you may offer support or warranty protection for a fee.

  5. Conveying Modified Source Versions.

  You may convey a work based on the Program, or the modifications to
produce it from the Program, in the form of source code under the
terms of section 4, provided that you also meet all of these conditions:

    a) The work must carry prominent notices stating that you modified
    it, and giving a relevant date.

    b) The work must carry prominent notices stating that it is
    released under this License and any conditions added under section
    7.  This requirement modifies the requirement in section 4 to
    "keep intact all notices".

    c) You must license the entire work, as a whole, under this
    License to anyone who comes into possession of a copy.  This
    License will therefore apply, along with any applicable section 7
    additional terms, to the whole of the work, and all its parts,
    regardless of how they are packaged.  This License gives no
    permission to license the work in any other way, but it does not
    invalidate such permission if you have separately received it.

    d) If the work has interactive user interfaces, each must display
    Appropriate Legal Notices; however, if the Program has interactive
    interfaces that do not display Appropriate Legal Notices, your
    work need not make them do so.

  A compilation of a covered work with other separate and independent
works, which are not by their nature extensions of the covered work,
and which are not combined with it such as to form a larger program,
in or on a volume of a storage or distribution medium, is called an
"aggregate" if the compilation and its resulting copyright are not
used to limit the access or legal rights of the compilation's users
beyond what the individual works permit.  Inclusion of a covered work
in an aggregate does not cause this License to apply to the other
parts of the aggregate.

  6. Conveying Non-Source Forms.

  You may convey a covered work in object code form under the terms
of sections 4 and 5, provided that you also convey the
machine-readable Corresponding Source under the terms of this License,
in one of these ways:

    a) Convey the object code in, or embodied in, a physical product
    (including a physical distribution medium), accompanied by the
    Corresponding Source fixed on a durable physical medium
    customarily used for software interchange.

    b) Convey the object code in, or embodied in, a physical product
    (including a physical distribution medium), accompanied by a
    written offer, valid for at least three years and valid for as
    long as you offer spare parts or customer support for that product
    model, to give anyone who possesses the object code either (1) a
    copy of the Corresponding Source for all the software in the
    product that is covered by this License, on a durable physical
    medium customarily used for software interchange, for a price no
    more than your reasonable cost of physically performing this
    conveying of source, or (2) access to copy the
    Corresponding Source from a network server at no charge.

    c) Convey individual copies of the object code with a copy of the
    written offer to provide the Corresponding Source.  This
    alternative is allowed only occasionally and noncommercially, and
    only if you received the object code with such an offer, in accord
    with subsection 6b.

    d) Convey the object code by offering access from a designated
    place (gratis or for a charge), and offer equivalent access to the
    Corresponding Source in the same way through the same place at no
    further charge.  You need not require recipients to copy the
    Corresponding Source along with the object code.  If the place to
    copy the object code is a network server, the Corresponding Source
    may be on a different server (operated by you or a third party)
    that supports equivalent copying facilities, provided you maintain
    clear directions next to the object code saying where to find the
    Corresponding Source.  Regardless of what server hosts the
    Corresponding Source, you remain obligated to ensure that it is
    available for as long as needed to satisfy these requirements.

    e) Convey the object code using peer-to-peer transmission, provided
    you inform other peers where the object code and Corresponding
    Source of the work are being offered to the general public at no
    charge under subsection 6d.

  A separable portion of the object code, whose source code is excluded
from the Corresponding Source as a System Library, need not be
included in conveying the object code work.

  A "User Product" is either (1) a "consumer product", which means any
tangible personal property which is normally used for personal, family,
or household purposes, or (2) anything designed or sold for incorporation
into a dwelling.  In determining whether a product is a consumer product,
doubtful cases shall be resolved in favor of coverage.  For a particular
product received by a particular user, "normally used" refers to a
typical or common use of that class of product, regardless of the status
of the particular user or of the way in which the particular user
actually uses, or expects or is expected to use, the product.  A product
is a consumer product regardless of whether the product has substantial
commercial, industrial or non-consumer uses, unless such uses represent
the only significant mode of use of the product.

  "Installation Information" for a User Product means any methods,
procedures, authorization keys, or other information required to install
and execute modified versions of a covered work in that User Product from
a modified version of its Corresponding Source.  The information must
suffice to ensure that the continued functioning of the modified object
code is in no case prevented or interfered with solely because
modification has been made.

  If you convey an object code work under this section in, or with, or
specifically for use in, a User Product, and the conveying occurs as
part of a transaction in which the right of possession and use of the
User Product is transferred to the recipient in perpetuity or for a
fixed term (regardless of how the transaction is characterized), the
Corresponding Source conveyed under this section must be accompanied
by the Installation Information.  But this requirement does not apply
if neither you nor any third party retains the ability to install
modified object code on the User Product (for example, the work has
been installed in ROM).

  The requirement to provide Installation Information does not include a
requirement to continue to provide support service, warranty, or updates
for a work that has been modified or installed by the recipient, or for
the User Product in which it has been modified or installed.  Access to a
network may be denied when the modification itself materially and
adversely affects the operation of the network or violates the rules and
protocols for communication across the network.

  Corresponding Source conveyed, and Installation Information provided,
in accord with this section must be in a format that is publicly
documented (and with an implementation available to the public in
source code form), and must require no special password or key for
unpacking, reading or copying.

  7. Additional Terms.

  "Additional permissions" are terms that supplement the terms of this
License by making exceptions from one or more of its conditions.
Additional permissions that are applicable to the entire Program shall
be treated as though they were included in this License, to the extent
that they are valid under applicable law.  If additional permissions
apply only to part of the Program, that part may be used separately
under those permissions, but the entire Program remains governed by
this License without regard to the additional permissions.

  When you convey a copy of a covered work, you may at your option
remove any additional permissions from that copy, or from any part of
it.  (Additional permissions may be written to require their own
removal in certain cases when you modify the work.)  You may place
additional permissions on material, added by you to a covered work,
for which you have or can give appropriate copyright permission.

  Notwithstanding any other provision of this License, for material you
add to a covered work, you may (if authorized by the copyright holders of
that material) supplement the terms of this License with terms:

    a) Disclaiming warranty or limiting liability differently from the
    terms of sections 15 and 16 of this License; or

    b) Requiring preservation of specified reasonable legal notices or
    author attributions in that material or in the Appropriate Legal
    Notices displayed by works containing it; or

    c) Prohibiting misrepresentation of the origin of that material, or
    requiring that modified versions of such material be marked in
    reasonable ways as different from the original version; or

    d) Limiting the use for publicity purposes of names of licensors or
    authors of the material; or

    e) Declining to grant rights under trademark law for use of some
    trade names, trademarks, or service marks; or

    f) Requiring indemnification of licensors and authors of that
    material by anyone who conveys the material (or modified versions of
    it) with contractual assumptions of liability to the recipient, for
    any liability that these contractual assumptions directly impose on
    those licensors and authors.

  All other non-permissive additional terms are considered "further
restrictions" within the meaning of section 10.  If the Program as you
received it, or any part of it, contains a notice stating that it is
governed by this License along with a term that is a further
restriction, you may remove that term.  If a license document contains
a further restriction but permits relicensing or conveying under this
License, you may add to a covered work material governed by the terms
of that license document, provided that the further restriction does
not survive such relicensing or conveying.

  If you add terms to a covered work in accord with this section, you
must place, in the relevant source files, a statement of the
additional terms that apply to those files, or a notice indicating
where to find the applicable terms.

  Additional terms, permissive or non-permissive, may be stated in the
form of a separately written license, or stated as exceptions;
the above requirements apply either way.

  8. Termination.

  You may not propagate or modify a covered work except as expressly
provided under this License.  Any attempt otherwise to propagate or
modify it is void, and will automatically terminate your rights under
this License (including any patent licenses granted under the third
paragraph of section 11).

  However, if you cease all violation of this License, then your
license from a particular copyright holder is reinstated (a)
provisionally, unless and until the copyright holder explicitly and
finally terminates your license, and (b) permanently, if the copyright
holder fails to notify you of the violation by some reasonable means
prior to 60 days after the cessation.

  Moreover, your license from a particular copyright holder is
reinstated permanently if the copyright holder notifies you of the
violation by some reasonable means, this is the first time you have
received notice of violation of this License (for any work) from that
copyright holder, and you cure the violation prior to 30 days after
your receipt of the notice.

  Termination of your rights under this section does not terminate the
licenses of parties who have received copies or rights from you under
this License.  If your rights have been terminated and not permanently
reinstated, you do not qualify to receive new licenses for the same
material under section 10.

  9. Acceptance Not Required for Having Copies.

  You are not required to accept this License in order to receive or
run a copy of the Program.  Ancillary propagation of a covered work
occurring solely as a consequence of using peer-to-peer transmission
to receive a copy likewise does not require acceptance.  However,
nothing other than this License grants you permission to propagate or
modify any covered work.  These actions infringe copyright if you do
not accept this License.  Therefore, by modifying or propagating a
covered work, you indicate your acceptance of this License to do so.

  10. Automatic Licensing of Downstream Recipients.

  Each time you convey a covered work, the recipient automatically
receives a license from the original licensors, to run, modify and
propagate that work, subject to this License.  You are not responsible
for enforcing compliance by third parties with this License.

  An "entity transaction" is a transaction transferring control of an
organization, or substantially all assets of one, or subdividing an
organization, or merging organizations.  If propagation of a covered
work results from an entity transaction, each party to that
transaction who receives a copy of the work also receives whatever
licenses to the work the party's predecessor in interest had or could
give under the previous paragraph, plus a right to possession of the
Corresponding Source of the work from the predecessor in interest, if
the predecessor has it or can get it with reasonable efforts.

  You may not impose any further restrictions on the exercise of the
rights granted or affirmed under this License.  For example, you may
not impose a license fee, royalty, or other charge for exercise of
rights granted under this License, and you may not initiate litigation
(including a cross-claim or counterclaim in a lawsuit) alleging that
any patent claim is infringed by making, using, selling, offering for
sale, or importing the Program or any portion of it.

  11. Patents.

  A "contributor" is a copyright holder who authorizes use under this
License of the Program or a work on which the Program is based.  The
work thus licensed is called the contributor's "contributor version".

  A contributor's "essential patent claims" are all patent claims
owned or controlled by the contributor, whether already acquired or
hereafter acquired, that would be infringed by some manner, permitted
by this License, of making, using, or selling its contributor version,
but do not include claims that would be infringed only as a
consequence of further modification of the contributor version.  For
purposes of this definition, "control" includes the right to grant
patent sublicenses in a manner consistent with the requirements of
this License.

  Each contributor grants you a non-exclusive, worldwide, royalty-free
patent license under the contributor's essential patent claims, to
make, use, sell, offer for sale, import and otherwise run, modify and
propagate the contents of its contributor version.

  In the following three paragraphs, a "patent license" is any express
agreement or commitment, however denominated, not to enforce a patent
(such as an express permission to practice a patent or covenant not to
sue for patent infringement).  To "grant" such a patent license to a
party means to make such an agreement or commitment not to enforce a
patent against the party.

  If you convey a covered work, knowingly relying on a patent license,
and the Corresponding Source of the work is not available for anyone
to copy, free of charge and under the terms of this License, through a
publicly available network server or other readily accessible means,
then you must either (1) cause the Corresponding Source to be so
available, or (2) arrange to deprive yourself of the benefit of the
patent license for this particular work, or (3) arrange, in a manner
consistent with the requirements of this License, to extend the patent
license to downstream recipients.  "Knowingly relying" means you have
actual knowledge that, but for the patent license, your conveying the
covered work in a country, or your recipient's use of the covered work
in a country, would infringe one or more identifiable patents in that
country that you have reason to believe are valid.

  If, pursuant to or in connection with a single transaction or
arrangement, you convey, or propagate by procuring conveyance of, a
covered work, and grant a patent license to some of the parties
receiving the covered work authorizing them to use, propagate, modify
or convey a specific copy of the covered work, then the patent license
you grant is automatically extended to all recipients of the covered
work and works based on it.

  A patent license is "discriminatory" if it does not include within
the scope of its coverage, prohibits the exercise of, or is
conditioned on the non-exercise of one or more of the rights that are
specifically granted under this License.  You may not convey a covered
work if you are a party to an arrangement with a third party that is
in the business of distributing software, under which you make payment
to the third party based on the extent of your activity of conveying
the work, and under which the third party grants, to any of the
parties who would receive the covered work from you, a discriminatory
patent license (a) in connection with copies of the covered work
conveyed by you (or copies made from those copies), or (b) primarily
for and in connection with specific products or compilations that
contain the covered work, unless you entered into that arrangement,
or that patent license was granted, prior to 28 March 2007.

  Nothing in this License shall be construed as excluding or limiting
any implied license or other defenses to infringement that may
otherwise be available to you under applicable patent law.

  12. No Surrender of Others' Freedom.

  If conditions are imposed on you (whether by court order, agreement or
otherwise) that contradict the conditions of this License, they do not
excuse you from the conditions of this License.  If you cannot convey a
covered work so as to satisfy simultaneously your obligations under this
License and any other pertinent obligations, then as a consequence you may
not convey it at all.  For example, if you agree to terms that obligate you
to collect a royalty for further conveying from those to whom you convey
the Program, the only way you could satisfy both those terms and this
License would be to refrain entirely from conveying the Program.

  13. Use with the GNU Affero General Public License.

  Notwithstanding any other provision of this License, you have
permission to link or combine any covered work with a work licensed
under version 3 of the GNU Affero General Public License into a single
combined work, and to convey the resulting work.  The terms of this
License will continue to apply to the part which is the covered work,
but the special requirements of the GNU Affero General Public License,
section 13, concerning interaction through a network will apply to the
combination as such.

  14. Revised Versions of this License.

  The Free Software Foundation may publish revised and/or new versions of
the GNU General Public License from time to time.  Such new versions will
be similar in spirit to the present version, but may differ in detail to
address new problems or concerns.

  Each version is given a distinguishing version number.  If the
Program specifies that a certain numbered version of the GNU General
Public License "or any later version" applies to it, you have the
option of following the terms and conditions either of that numbered
version or of any later version published by the Free Software
Foundation.  If the Program does not specify a version number of the
GNU General Public License, you may choose any version ever published
by the Free Software Foundation.

  If the Program specifies that a proxy can decide which future
versions of the GNU General Public License can be used, that proxy's
public statement of acceptance of a version permanently authorizes you
to choose that version for the Program.

  Later license versions may give you additional or different
permissions.  However, no additional obligations are imposed on any
author or copyright holder as a result of your choosing to follow a
later version.

  15. Disclaimer of Warranty.

  THERE IS NO WARRANTY FOR THE PROGRAM, TO THE EXTENT PERMITTED BY
APPLICABLE LAW.  EXCEPT WHEN OTHERWISE STATED IN WRITING THE COPYRIGHT
HOLDERS AND/OR OTHER PARTIES PROVIDE THE PROGRAM "AS IS" WITHOUT WARRANTY
OF ANY KIND, EITHER EXPRESSED OR IMPLIED, INCLUDING, BUT NOT LIMITED TO,
THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
PURPOSE.  THE ENTIRE RISK AS TO THE QUALITY AND PERFORMANCE OF THE PROGRAM
IS WITH YOU.  SHOULD THE PROGRAM PROVE DEFECTIVE, YOU ASSUME THE COST OF
ALL NECESSARY SERVICING, REPAIR OR CORRECTION.

  16. Limitation of Liability.

  IN NO EVENT UNLESS REQUIRED BY APPLICABLE LAW OR AGREED TO IN WRITING
WILL ANY COPYRIGHT HOLDER, OR ANY OTHER PARTY WHO MODIFIES AND/OR CONVEYS
THE PROGRAM AS PERMITTED ABOVE, BE LIABLE TO YOU FOR DAMAGES, INCLUDING ANY
GENERAL, SPECIAL, INCIDENTAL OR CONSEQUENTIAL DAMAGES ARISING OUT OF THE
USE OR INABILITY TO USE THE PROGRAM (INCLUDING BUT NOT LIMITED TO LOSS OF
DATA OR DATA BEING RENDERED INACCURATE OR LOSSES SUSTAINED BY YOU OR THIRD
PARTIES OR A FAILURE OF THE PROGRAM TO OPERATE WITH ANY OTHER PROGRAMS),
EVEN IF SUCH HOLDER OR OTHER PARTY HAS BEEN ADVISED OF THE POSSIBILITY OF
SUCH DAMAGES.

  17. Interpretation of Sections 15 and 16.

  If the disclaimer of warranty and limitation of liability provided
above cannot be given local legal effect according to their terms,
reviewing courts shall apply local law that most closely approximates
an absolute waiver of all civil liability in connection with the
Program, unless a warranty or assumption of liability accompanies a
copy of the Program in return for a fee.

                     END OF TERMS AND CONDITIONS

            How to Apply These Terms to Your New Programs

  If you develop a new program, and you want it to be of the greatest
possible use to the public, the best way to achieve this is to make it
free software which everyone can redistribute and change under these terms.

  To do so, attach the following notices to the program.  It is safest
to attach them to the start of each source file to most effectively
state the exclusion of warranty; and each file should have at least
the "copyright" line and a pointer to where the full notice is found.

    <one line to give the program's name and a brief idea of what it does.>
    Copyright (C) <year>  <name of author>

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <https://www.gnu.org/licenses/>.

Also add information on how to contact you by electronic and paper mail.

  If the program does terminal interaction, make it output a short
notice like this when it starts in an interactive mode:

    <program>  Copyright (C) <year>  <name of author>
    This program comes with ABSOLUTELY NO WARRANTY; for details type `show w'.
    This is free software, and you are welcome to redistribute it
    under certain conditions; type `show c' for details.

The hypothetical commands `show w' and `show c' should show the appropriate
parts of the General Public License.  Of course, your program's commands
might be different; for a GUI interface, you would use an "about box".

  You should also get your employer (if you work as a programmer) or school,
if any, to sign a "copyright disclaimer" for the program, if necessary.
For more information on this, and how to apply and follow the GNU GPL, see
<https://www.gnu.org/licenses/>.

  The GNU General Public License does not permit incorporating your program
into proprietary programs.  If your program is a subroutine library, you
may consider it more useful to permit linking proprietary applications with
the library.  If this is what you want to do, use the GNU Lesser General
Public License instead of this License.  But first, please read
<https://www.gnu.org/licenses/why-not-lgpl.html>.
"""
# the full CC0 1.0 Universal legal code, for the scores (served at /license/cc0)
CC0_TEXT = """Creative Commons Legal Code

CC0 1.0 Universal

    CREATIVE COMMONS CORPORATION IS NOT A LAW FIRM AND DOES NOT PROVIDE
    LEGAL SERVICES. DISTRIBUTION OF THIS DOCUMENT DOES NOT CREATE AN
    ATTORNEY-CLIENT RELATIONSHIP. CREATIVE COMMONS PROVIDES THIS
    INFORMATION ON AN "AS-IS" BASIS. CREATIVE COMMONS MAKES NO WARRANTIES
    REGARDING THE USE OF THIS DOCUMENT OR THE INFORMATION OR WORKS
    PROVIDED HEREUNDER, AND DISCLAIMS LIABILITY FOR DAMAGES RESULTING FROM
    THE USE OF THIS DOCUMENT OR THE INFORMATION OR WORKS PROVIDED
    HEREUNDER.

Statement of Purpose

The laws of most jurisdictions throughout the world automatically confer
exclusive Copyright and Related Rights (defined below) upon the creator
and subsequent owner(s) (each and all, an "owner") of an original work of
authorship and/or a database (each, a "Work").

Certain owners wish to permanently relinquish those rights to a Work for
the purpose of contributing to a commons of creative, cultural and
scientific works ("Commons") that the public can reliably and without fear
of later claims of infringement build upon, modify, incorporate in other
works, reuse and redistribute as freely as possible in any form whatsoever
and for any purposes, including without limitation commercial purposes.
These owners may contribute to the Commons to promote the ideal of a free
culture and the further production of creative, cultural and scientific
works, or to gain reputation or greater distribution for their Work in
part through the use and efforts of others.

For these and/or other purposes and motivations, and without any
expectation of additional consideration or compensation, the person
associating CC0 with a Work (the "Affirmer"), to the extent that he or she
is an owner of Copyright and Related Rights in the Work, voluntarily
elects to apply CC0 to the Work and publicly distribute the Work under its
terms, with knowledge of his or her Copyright and Related Rights in the
Work and the meaning and intended legal effect of CC0 on those rights.

1. Copyright and Related Rights. A Work made available under CC0 may be
protected by copyright and related or neighboring rights ("Copyright and
Related Rights"). Copyright and Related Rights include, but are not
limited to, the following:

  i. the right to reproduce, adapt, distribute, perform, display,
     communicate, and translate a Work;
 ii. moral rights retained by the original author(s) and/or performer(s);
iii. publicity and privacy rights pertaining to a person's image or
     likeness depicted in a Work;
 iv. rights protecting against unfair competition in regards to a Work,
     subject to the limitations in paragraph 4(a), below;
  v. rights protecting the extraction, dissemination, use and reuse of data
     in a Work;
 vi. database rights (such as those arising under Directive 96/9/EC of the
     European Parliament and of the Council of 11 March 1996 on the legal
     protection of databases, and under any national implementation
     thereof, including any amended or successor version of such
     directive); and
vii. other similar, equivalent or corresponding rights throughout the
     world based on applicable law or treaty, and any national
     implementations thereof.

2. Waiver. To the greatest extent permitted by, but not in contravention
of, applicable law, Affirmer hereby overtly, fully, permanently,
irrevocably and unconditionally waives, abandons, and surrenders all of
Affirmer's Copyright and Related Rights and associated claims and causes
of action, whether now known or unknown (including existing as well as
future claims and causes of action), in the Work (i) in all territories
worldwide, (ii) for the maximum duration provided by applicable law or
treaty (including future time extensions), (iii) in any current or future
medium and for any number of copies, and (iv) for any purpose whatsoever,
including without limitation commercial, advertising or promotional
purposes (the "Waiver"). Affirmer makes the Waiver for the benefit of each
member of the public at large and to the detriment of Affirmer's heirs and
successors, fully intending that such Waiver shall not be subject to
revocation, rescission, cancellation, termination, or any other legal or
equitable action to disrupt the quiet enjoyment of the Work by the public
as contemplated by Affirmer's express Statement of Purpose.

3. Public License Fallback. Should any part of the Waiver for any reason
be judged legally invalid or ineffective under applicable law, then the
Waiver shall be preserved to the maximum extent permitted taking into
account Affirmer's express Statement of Purpose. In addition, to the
extent the Waiver is so judged Affirmer hereby grants to each affected
person a royalty-free, non transferable, non sublicensable, non exclusive,
irrevocable and unconditional license to exercise Affirmer's Copyright and
Related Rights in the Work (i) in all territories worldwide, (ii) for the
maximum duration provided by applicable law or treaty (including future
time extensions), (iii) in any current or future medium and for any number
of copies, and (iv) for any purpose whatsoever, including without
limitation commercial, advertising or promotional purposes (the
"License"). The License shall be deemed effective as of the date CC0 was
applied by Affirmer to the Work. Should any part of the License for any
reason be judged legally invalid or ineffective under applicable law, such
partial invalidity or ineffectiveness shall not invalidate the remainder
of the License, and in such case Affirmer hereby affirms that he or she
will not (i) exercise any of his or her remaining Copyright and Related
Rights in the Work or (ii) assert any associated claims and causes of
action with respect to the Work, in either case contrary to Affirmer's
express Statement of Purpose.

4. Limitations and Disclaimers.

 a. No trademark or patent rights held by Affirmer are waived, abandoned,
    surrendered, licensed or otherwise affected by this document.
 b. Affirmer offers the Work as-is and makes no representations or
    warranties of any kind concerning the Work, express, implied,
    statutory or otherwise, including without limitation warranties of
    title, merchantability, fitness for a particular purpose, non
    infringement, or the absence of latent or other defects, accuracy, or
    the present or absence of errors, whether or not discoverable, all to
    the greatest extent permissible under applicable law.
 c. Affirmer disclaims responsibility for clearing rights of other persons
    that may apply to the Work or any use thereof, including without
    limitation any person's Copyright and Related Rights in the Work.
    Further, Affirmer disclaims responsibility for obtaining any necessary
    consents, permissions or other rights required for any use of the
    Work.
 d. Affirmer understands and acknowledges that Creative Commons is not a
    party to this document and has no duty or obligation with respect to
    this CC0 or use of the Work.
"""

# Python packages that go into the built app with the window (pywebview and what it needs)
WINDOW_PACKAGES = ["pywebview"]


def _license_name(meta):
    """A short license name from a package's metadata."""
    expr = meta.get("License-Expression")
    if expr:
        return expr
    lic = (meta.get("License") or "").strip()
    if lic and len(lic) < 60 and "\n" not in lic:
        return lic
    for c in meta.get_all("Classifier") or []:
        if c.startswith("License :: ") and "OSI Approved :: " in c:
            return c.split(" :: ")[-1]
    return "see the package"


def installed_window_packages():
    """When run as a script: pywebview and the packages it needs, if installed here."""
    try:
        from importlib import metadata
    except ImportError:
        return []
    out, todo, seen = [], list(WINDOW_PACKAGES), set()
    while todo:
        name = todo.pop(0)
        key = name.lower().replace("_", "-")
        if key in seen:
            continue
        seen.add(key)
        try:
            dist = metadata.distribution(name)
        except Exception:
            continue
        meta = dist.metadata
        home = meta.get("Home-page") or ""
        for u in meta.get_all("Project-URL") or []:
            if not home and "," in u:
                home = u.split(",", 1)[1].strip()
        out.append({"name": meta.get("Name") or name, "version": dist.version,
                    "license": _license_name(meta), "summary": meta.get("Summary") or "",
                    "home": home, "files": []})
        for req in dist.requires or []:
            try:
                from packaging.requirements import Requirement
                r = Requirement(req)
                if r.marker and not r.marker.evaluate({"extra": ""}):
                    continue
                todo.append(r.name)
            except Exception:
                if "extra ==" not in req:
                    todo.append(re.split(r"[\s;<>=!~\[(]", req, 1)[0])
    return out


def bundled_packages():
    """(packages, other items, bundled?) for the Acknowledgements page: in the built app,
    the list the build wrote (licenses/python-packages/index.json); as a script, what's
    installed on this computer."""
    d = app_licenses_dir()
    index = os.path.join(d, "python-packages", "index.json") if d else ""
    if index and os.path.isfile(index):
        try:
            with open(index, encoding="utf-8") as f:
                data = json.load(f)
            return data.get("packages", []), data.get("extras", []), True
        except (OSError, ValueError):
            pass
    return installed_window_packages(), [], False

# ---------------- the Harmonarium logo (from harmonarium-light.svg / -dark.svg) ----------------
# The mark: three stacked ellipses (chords) on one vertical axis, with dots for the notes.
# Drawn in currentColor, so it takes the panel's ink colour in light and dark mode.
LOGO_ELLIPSES = [(280.0, 65.0, 140.0, 36.0), (280.0, 108.0, 140.0, 36.0), (280.0, 151.0, 140.0, 36.0)]
LOGO_DOTS = [(280.0, 29.0, 8.0), (280.0, 65.0, 8.0), (280.0, 95.0, 8.0), (280.0, 116.0, 8.0), (280.0, 151.0, 8.0), (280.0, 187.0, 8.0), (140.0, 108.0, 8.0), (420.0, 108.0, 8.0)]
LOGO_AXIS = "M 280 18 V 195"
LOGO_WORDMARK = "m 144.72397,250 h -2.262 v -13.572 h -15.873 V 250 h -2.262 v -27.846 h 2.262 V 234.4 h 15.873 v -12.246 h 2.262 z m 32.27204,0 -3.705,-9.594 h -11.544 l -3.744,9.594 h -2.34 l 10.959,-27.963 h 2.067 l 10.686,27.963 z m -8.112,-21.684 q -0.234,-0.546 -0.624,-1.716 -0.39,-1.17 -0.663,-2.067 -0.312,1.053 -0.663,2.067 -0.351,1.014 -0.585,1.755 l -3.861,9.984 h 10.101 z m 28.33299,-6.162 q 4.992,0 7.488,1.755 2.535,1.716 2.535,5.889 0,3.198 -1.716,5.031 -1.677,1.794 -4.212,2.535 L 208.956,250 h -2.691 l -7.098,-12.012 h -6.63 V 250 h -2.262 v -27.846 z m -0.195,1.989 h -4.485 v 11.895 h 5.265 q 3.393,0 5.226,-1.56 1.872,-1.599 1.872,-4.602 0,-3.198 -1.95,-4.446 -1.95,-1.287 -5.928,-1.287 z m 35.74302,25.857 -9.984,-25.467 h -0.117 q 0.039,1.092 0.078,2.496 0.078,1.365 0.078,2.886 V 250 h -2.145 v -27.846 h 3.432 l 9.594,24.375 h 0.117 l 9.711,-24.375 h 3.354 V 250 h -2.262 v -20.319 q 0,-1.287 0.039,-2.613 0.078,-1.365 0.117,-2.496 h -0.117 L 234.59802,250 Z M 285.278,236.038 q 0,4.251 -1.404,7.488 -1.404,3.237 -4.212,5.07 -2.769,1.794 -6.903,1.794 -4.212,0 -7.02,-1.794 -2.769,-1.833 -4.173,-5.07 -1.365,-3.276 -1.365,-7.527 0,-4.251 1.404,-7.449 1.443,-3.198 4.251,-4.992 2.847,-1.833 7.02,-1.833 4.017,0 6.786,1.755 2.769,1.716 4.173,4.914 1.443,3.198 1.443,7.644 z m -22.698,-0.039 q 0,3.705 1.092,6.513 1.092,2.769 3.354,4.329 2.262,1.521 5.733,1.521 3.51,0 5.733,-1.521 2.262,-1.521 3.315,-4.29 1.092,-2.808 1.092,-6.513 0,-5.811 -2.535,-9.048 -2.496,-3.237 -7.488,-3.237 -3.471,0 -5.772,1.56 -2.301,1.521 -3.432,4.29 -1.092,2.73 -1.092,6.396 z M 319.26599,250 h -2.418 l -16.146,-24.336 h -0.117 q 0.078,1.521 0.117,3.237 0.078,1.677 0.078,3.51 V 250 h -2.145 v -27.846 h 2.418 l 16.107,24.258 h 0.117 q -0.078,-1.209 -0.117,-3.081 -0.039,-1.872 -0.039,-3.51 v -17.667 h 2.145 z m 32.233,0 -3.705,-9.594 h -11.544 l -3.744,9.594 h -2.34 l 10.959,-27.963 h 2.067 l 10.686,27.963 z m -8.112,-21.684 q -0.234,-0.546 -0.624,-1.716 -0.39,-1.17 -0.663,-2.067 -0.312,1.053 -0.663,2.067 -0.351,1.014 -0.585,1.755 l -3.861,9.984 h 10.101 z m 28.333,-6.162 q 4.992,0 7.488,1.755 2.535,1.716 2.535,5.889 0,3.198 -1.716,5.031 -1.677,1.794 -4.212,2.535 l 7.644,12.636 h -2.691 l -7.098,-12.012 h -6.63 V 250 h -2.262 v -27.846 z m -0.195,1.989 h -4.485 v 11.895 h 5.265 q 3.393,0 5.226,-1.56 1.872,-1.599 1.872,-4.602 0,-3.198 -1.95,-4.446 -1.95,-1.287 -5.928,-1.287 z M 401.45698,250 h -8.19 v -1.404 l 2.964,-0.429 v -24.141 l -2.964,-0.468 v -1.404 h 8.19 v 1.404 l -2.964,0.468 v 24.141 l 2.964,0.429 z m 33.48106,-9.828 q 0,4.758 -2.769,7.488 -2.73,2.73 -7.761,2.73 -5.031,0 -7.722,-2.73 -2.652,-2.73 -2.652,-7.566 v -17.94 h 2.262 v 17.94 q 0,4.056 2.106,6.162 2.106,2.106 6.123,2.106 3.939,0 6.045,-2.106 2.145,-2.145 2.145,-5.928 v -18.174 h 2.223 z m 26.61699,9.828 -9.984,-25.467 h -0.117 q 0.039,1.092 0.078,2.496 0.078,1.365 0.078,2.886 V 250 h -2.145 v -27.846 h 3.432 l 9.594,24.375 h 0.117 l 9.711,-24.375 h 3.354 V 250 h -2.262 v -20.319 q 0,-1.287 0.039,-2.613 0.078,-1.365 0.117,-2.496 h -0.117 L 463.38803,250 Z"


def harmonarium_mark(colour="currentColor", stroke=2.7, dot_scale=1.0):
    """The mark alone (no wordmark), in the logo's own 600 x 280 coordinates."""
    out = [f'<g fill="none" stroke="{colour}" stroke-width="{stroke}">']
    out += [f'<ellipse cx="{cx:g}" cy="{cy:g}" rx="{rx:g}" ry="{ry:g}"/>' for cx, cy, rx, ry in LOGO_ELLIPSES]
    out.append(f'<path d="{LOGO_AXIS}"/></g><g fill="{colour}">')
    out += [f'<circle cx="{cx:g}" cy="{cy:g}" r="{r * dot_scale:g}"/>' for cx, cy, r in LOGO_DOTS]
    out.append("</g>")
    return "".join(out)


def harmonarium_logo_svg(colour="currentColor", cls="logo"):
    """The full logo with the HARMONARIUM wordmark, cropped to its drawing."""
    return (f'<svg class="{cls}" viewBox="116 14 368 244" role="img" aria-hidden="true" focusable="false">'
            + harmonarium_mark(colour)
            + f'<path d="{LOGO_WORDMARK}" fill="{colour}"/></svg>')


def harmonarium_icon_svg(size=1024, tile="#141414", ink="#ffffff", margin=0.0, small=False):
    """The app icon: the mark alone on a rounded tile. Small sizes get heavier lines and
    bigger dots so the mark stays readable at 16-48 px. margin: Mac icons leave about 10%."""
    t0, t1 = 32 + margin * 1024, 992 - margin * 1024           # the tile, in 1024 units
    w = t1 - t0
    stroke, dots = (7.5, 1.55) if small else (3.4, 1.15)
    # the mark spans x 132-428, y 18-195 (296 x 177): fit its width to about 74% of the tile
    k = (0.88 if small else 0.74) * w / 296
    tx = t0 + (w - 296 * k) / 2 - 132 * k
    ty = t0 + (w - 177 * k) / 2 - 18 * k
    return (f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 1024 1024" width="{size}" height="{size}">'
            f'<rect x="{t0:g}" y="{t0:g}" width="{w:g}" height="{w:g}" rx="{w * 0.198:g}" fill="{tile}"/>'
            f'<g transform="translate({tx:.2f} {ty:.2f}) scale({k:.4f})">'
            + harmonarium_mark(ink, stroke, dots) + "</g></svg>")


# ---------------- the panel's font: Academico (embedded, unmodified) ----------------
# Academico Regular and Bold, Version 0.905, the original .otf files byte for byte (base64).
# Copyright (c) 2017-2025 Steinberg Media Technologies GmbH, with Reserved Font Name "Academico".
# Licensed under the SIL Open Font License 1.1 (ACADEMICO_LICENSE below; also shown on the
# Acknowledgements page). From https://github.com/dbenjaminmiller/academico-mirror
import base64 as _b64
ACADEMICO_REGULAR = _b64.b64decode("""
T1RUTwANAIAAAwBQQ0ZGIHvQrhwAAA0gAACD0URTSUcAAAACAADm+AAAAAhHREVGCr4MTQAA2cAAAABeR1BPU2ILUGIAANogAAAM
FEdTVUK5hr9KAADmNAAAAMRPUy8ybyOFyQAAAUAAAABgY21hcAaTxfwAAAg0AAAE7GhlYWQqWWzSAAAA3AAAADZoaGVhB2sERgAA
ARQAAAAkaG10eK5sLrYAAAGgAAAGlG1heHABpVAAAAABOAAAAAZuYW1l9Wd5xwAAkPQAAEipcG9zdP+4ADIAANmgAAAAIAABAAAA
AOeu7vvP118PPPUAAwPoAAAAAOPXnuMAAAAA49eiCf89/rQEVgSkAAAAAwACAAAAAAAAAAEAAAPU/wYAAARd/z3/PQRXAAEAAAAA
AAAAAAAAAAAAAAGlAABQAAGlAAAABAI+AZAABQAAAooCWAAAAEsCigJYAAABXgAyARYAAAIEBgMFBwUCAwQAAAAHAAAAAAAAAAAA
AAAAU01URwBAAAD7AgLu/wYA5gPUAPogAAABAAAAAAHQAtIAAAAgAAIBFgAAAAAAAAEWAAABFgAAASgAVgGFAD0CLAAcAiwALQNB
ADoDLwAzAMwAOwFNACgBTQA2AfQAOQJeADIAvQAdASAAKgEWAE0A3P/gAiwAKgIsAGQCLAAjAiwAKgIsABwCLAAuAiwAKQIsADsC
LAAqAiwAKQEWAE0BFgA+Al4AMgJeADICXgAyAbwAHQLh//gC0v/4AtIAHQLSAC0DCgAdAtIAHQKbAB0DCgAtA0EAHQGXACYCLAAF
AwoAHQKbAB0DsAAdAy8AGAMKAC0CmwAdAwoALQLSAB0CdgAvApsAEwMvABAC0v/4A9UABQLA//gCwP/1AmMAGAFNAH4A3P/gAU0A
EgJeAFkB9AAAAU0AEQIsACwCLAAKAbwAIgI+ACIB9AAiAU0AEgIZABcCYwAHATsAEgD2/6oCUQAKATsAEgN5ABoCYwAWAfQAIgI+
ABYCLAAiAbwAEgHPAC4BhQASAmMAFgIZ//oDCgABAhkACAIZAAQB4QAqAU0ANgJeAQsBTQA2Al4ASAEoAFYBtwAiAp0ALQM+AHEB
igAZAU0AEANB//YBTv/8AaoAKAJeADIC4f/4AU0ACgGQADkCXgAyAU0AWwJjABYCXgA8ARYARwFNAB0BAf/zAaoAJwMSAB0DGQAd
AwQAFQG8AB0C0v/4AtL/+ALS//gC0v/4AtL/+ALS//gD6AAAAtIALQLSAB0C0gAdAtIAHQLSAB0BlwAmAZcAJgGXACYBlwAmAwoA
HQMvABgDCgAtAwoALQMKAC0DCgAtAwoALQMKAC0DLwAQAy8AEAMvABADLwAQAsD/9QKbAB0CPgAeAiwALAIsACwCLAAsAiwALAIs
ACwCLAAsAxwAIgG8ACIB9AAiAfQAIgH0ACIB9AAiATsACAE7ABIBOwABATsABwH0ACICYwAWAfQAIgH0ACIB9AAiAfQAIgH0ACIC
XgAyAfQAIgJjABYCYwAWAmMAFgJjABYCGQAEAj4AFgIZAAQC0v/4AiwALALS//gCLAAsAtL/+AIsACwC0gAtAbwAIgLSAC0BvAAi
AtIALQG8ACIC0gAtAbwAIgMKAB0CSwAiAwoAHQI+ACIC0gAdAfQAIgLSAB0B9AAiAtIAHQH0ACIC0gAdAfQAIgLSAB0B9AAiAwoA
LQIZABcDCgAtAhkAFwMKAC0CGQAXAwoALQIZABcDQQAdAmMABwNBAAwCYwABAZcAJgE7//sBlwAmATsAAQGXACYBOwASAZcAJgE7
ABIBlwAmATsAEgPDACYCMQASAiwABQD2/6oDCgAdAlEACgKbAB0BOwASApsAHQE7ABICmwAdAVgAEgKbAB0BPQASApsAHQE7ABID
LwAYAmMAFgMvABgCYwAWAy8AGAJjABYDKgAYAmMAFgMKAC0B9AAiAwoALQH0ACIDCgAtAfQAIgPoABUDQQAiAtIAHQG8ABIC0gAd
AbwAEgLSAB0BvAASAnYALwHPAC4CdgAvAc8ALgJ2AC8BzwAuAlwALwHPAC4CmwATAYUAEgKbABMBgQASAy8AEAJjABYDLwAQAmMA
FgMvABACYwAWAy8AEAJjABYDLwAQAmMAFgMvABACYwAWA9UABQMKAAECwP/1AhkABALA//UCYwAYAeEAKgJjABgB4QAqAmMAGAHh
ACoBTQASAtIAHQJrAAADCgAtAfQAIgMvABACYwAWAtL/+AIsACwBlwAmATsAAAMKAC0B9AAiAy8AEAJjABYDLwAQAmMAFgMvABAC
YwAWAy8AEAJjABYB9AAiAwoALQIZABcDCgAtAfQAIgD2/6oDCgAtAhkAFwLS//gCLAAsBDQAAAMcACIC7gAtAfQAIgLS//gCPwAs
AqEAHQH9ACIBnAAmAUn/8wL2AC0B9QAiAucAHQHTABIDGgAQAmoAFgJ2AC8BzwAuApsAEwGFABIA9v+qAfQAIgH0ACIBXwAqAV8A
KgFNAAoBTQAKAU0AGQFNAHQBTQBCAU0AUQFNAAEBTf/3AzIAMQKxADcCLAAAA+gAAADMABkAzAAZAMwAGQGFABkBhQAZAYUAGQH0
ACsB9AArAl4AegMzAEoEXQArAOgAHgGSAB4BAwAoAQMAJwCn/z0CLAANA+gAIAMFAB0CFwA8An4AIgK0ABoCLAAcAikAIALzAC8B
fgARAhkAJgKKADICkwAyApMAMgH7ADEBqwAoASwAKAGQACgCYwASAmMAEgJjABICYwASApsAHQE7ABICdgAvAc8ALgJjABgB4QAq
AAAAAwAAAAMAAAImAAEAAAAAABwAAwABAAACJgAGAgoAAAAAAQAAAQAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA
AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAMABAAFAAYABwAIAAkACgALAAwADQAOAA8AEAARABIAEwAUABUAFgAXABgAGQAa
ABsAHAAdAB4AHwAgACEAIgAjACQAJQAmACcAKAApACoAKwAsAC0ALgAvADAAMQAyADMANAA1ADYANwA4ADkAOgA7ADwAPQA+AD8A
QABBAEIAQwBEAEUARgBHAEgASQBKAEsATABNAE4ATwBQAFEAUgBTAFQAVQBWAFcAWABZAFoAWwBcAF0AXgBfAGAAYQAAAH8AgACC
AIQAjACRAJYAmwCaAJwAngCdAJ8AoQCjAKIApAClAKcApgCoAKkAqwCtAKwArgCwAK8AtACzALUAtgF/AG4AYwBkAGYBgQByAJkA
bABoAYoAcABnAZQAgQCSAZEAbwGVAZYAZQBxAYwBjwGOAXYBkgBpAHUAAACgALIAegBiAGsBkAE3AZMBjQBqAHYBggAAAHsAfgCQ
AQoBCwF3AXgBfAF9AXkBegCxAZcAuQEuAYgBiQGGAYcBmwGcAYAAcwF7AX4BgwB9AIUAfACGAIMAiACJAIoAhwCOAI8AAACNAJQA
lQCTAOsBbQFzAG0BbwFwAXEAdAF0AXIBbgAEAsYAAAB8AEAABQA8AAAAfgCjAKUArACxALgA1gE3AUgBZQF/AY4BkgGhAbAB1AHd
AecB6wHwAfUCAQIFAgkCDQIRAhUCGwI3AlkCvwLHAt0DqQPAIBQgGiAeICIgJiAwIDMgOiBEIKwhIiFbIgIiBiIPIhEiGiIeIisi
SCJgImUlyiZv+wL//wAAAAAAIAChAKUApwCuALQAugDYATkBSgFoAY4BkgGgAa8BzQHXAeYB6gHwAfQB+gIEAggCDAIQAhQCGAI3
AlgCvgLGAtgDqQPAIBMgGCAcICAgJiAwIDIgOSBEIKwhIiFbIgIiBiIPIhEiGiIeIisiSCJgImQlyiZt+wH//wAB/+MAAP/AAAAA
AAAA/7v/uv+5/7j/tv+o/6UAAAAAAAAAAAAAAAD/XwAAAAAAAAAAAAAAAAAAAAD/MQAAAAAAAAAA/cz9tgAAAAAAAAAA4VzhUwAA
AADhRODd4GjgMN+K34fff99+33bfc99n30vfNAAA280AAAAAAAEAAAAAAHgAAAB6AIQAigAAAAAAAAAAAAAAAAAAAIQAhgCIAJYA
ogCkAAAApACmALQAtgC4ALoAvAC+AAAAwgDEAMYAyAAAAAAAzgDQANQA2AAAAAAA2ADaAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA
AAAAwgAAAMIAxgAAAGIAYwBkAGYAZwBoAGkAagBrAGwAbQBuAG8AcABxAHIAcwB0ATgBOQE6ATsBPAE9AT4BPwFAAUEBQgFDAUQB
RQFGAUcBSAFJAUoBSwFMAU0BTgFQAVEBUgFTAVQBVQFWAVcBWAFZAVoBWwFcAV0BXgFfAWABYQFiAWMBZAFlAWYBZwFpAWoBawFs
AW0BbgFvAXABcQFyAXMBdAF3AXgBeQF6AXsBfAF9AX4BfwGAAYEBhAGFAYYBhwGVAZYBmAGZAZoBmwGcAQAEAgABAQEKQWNhZGVt
aWNvAAEBASv44gD44wwA+OQC+OQD+OUEHP89HP60HARXHASkBRwsyA8cLjcRrxx3ABIAywIAAQAIAAoAEQAYAB8AJQArADIAOQA/
AEUAUABbAGUAbwB1AHsAgQCHAI0AkwCaAKEApwCtALcAwQDIAM8A1QDbAOYA8QD3AP0BBwERARgBHwEqATUBOQE9AUMBSQFQAVcB
XQFjAWoBcQF7AX0BfwGKAZUBnAGjAakBrwG2Ab0BwwHJAc0B0QHXAd0B5AHrAfEB9wH6Af0CBAILAhECFwIkAjECNwI9AkQCSwJR
AlcCXQJjAm4CeQKBAokCkAKXAp0CowKpAq8CtgK9AsMCyQLOAtMC4ALtAvQC+wMGAxEDHAMnAy0DMwM9A0cDTANTA1gDXQNiA2cD
bgN1A3wDgwOKA5EDmAOfA6YDrQO0A7sDwgPJA9AD1gPcA+MD6gPxA/gD/wQJBBMEGgQhBCwENwQ+BEUETARTBFoEYQRoBG8EdgR9
BIQEiwSSBJkEoASnBK4EtQS8BMMEygTRBNME2QTfBOME7gT1BPwFBQUMBRQFHAUnBS8FOAVEBUsFUgVZBWAFYwVmBXAFegWEBY4F
mAWiBa8XEhcbFyF1bmkwMDAwQ1J1bmkwMEI1QW1hY3JvbmFtYWNyb25BYnJldmVhYnJldmVBb2dvbmVrYW9nb25la0NhY3V0ZWNh
Y3V0ZUNjaXJjdW1mbGV4Y2NpcmN1bWZsZXhDZG90YWNjZW50Y2RvdGFjY2VudENjYXJvbmNjYXJvbkRjYXJvbmRjYXJvbkRjcm9h
dGRjcm9hdEVtYWNyb25lbWFjcm9uRWJyZXZlZWJyZXZlRWRvdGFjY2VudGVkb3RhY2NlbnRFb2dvbmVrZW9nb25la0VjYXJvbmVj
YXJvbkdjaXJjdW1mbGV4Z2NpcmN1bWZsZXhHYnJldmVnYnJldmVHZG90YWNjZW50Z2RvdGFjY2VudHVuaTAxMjJ1bmkwMTIzSGNp
cmN1bWZsZXhoY2lyY3VtZmxleEhiYXJoYmFySXRpbGRlaXRpbGRlSW1hY3JvbmltYWNyb25JYnJldmVpYnJldmVJb2dvbmVraW9n
b25la0lkb3RhY2NlbnRJSmlqSmNpcmN1bWZsZXhqY2lyY3VtZmxleHVuaTAxMzZ1bmkwMTM3TGFjdXRlbGFjdXRldW5pMDEzQnVu
aTAxM0NMY2Fyb25sY2Fyb25MZG90bGRvdE5hY3V0ZW5hY3V0ZXVuaTAxNDV1bmkwMTQ2TmNhcm9ubmNhcm9uRW5nZW5nT21hY3Jv
bm9tYWNyb25PYnJldmVvYnJldmVPaHVuZ2FydW1sYXV0b2h1bmdhcnVtbGF1dFJhY3V0ZXJhY3V0ZXVuaTAxNTZ1bmkwMTU3UmNh
cm9ucmNhcm9uU2FjdXRlc2FjdXRlU2NpcmN1bWZsZXhzY2lyY3VtZmxleFNjZWRpbGxhc2NlZGlsbGF1bmkwMTYydW5pMDE2M1Rj
YXJvbnRjYXJvblV0aWxkZXV0aWxkZVVtYWNyb251bWFjcm9uVWJyZXZldWJyZXZlVXJpbmd1cmluZ1VodW5nYXJ1bWxhdXR1aHVu
Z2FydW1sYXV0VW9nb25la3VvZ29uZWtXY2lyY3VtZmxleHdjaXJjdW1mbGV4WWNpcmN1bWZsZXh5Y2lyY3VtZmxleFphY3V0ZXph
Y3V0ZVpkb3RhY2NlbnR6ZG90YWNjZW50bG9uZ3N1bmkwMThFT2hvcm5vaG9yblVob3JudWhvcm51bmkwMUNEdW5pMDFDRXVuaTAx
Q0Z1bmkwMUQwdW5pMDFEMXVuaTAxRDJ1bmkwMUQzdW5pMDFENHVuaTAxRDd1bmkwMUQ4dW5pMDFEOXVuaTAxREF1bmkwMURCdW5p
MDFEQ3VuaTAxRERHY2Fyb25nY2Fyb251bmkwMUVBdW5pMDFFQnVuaTAxRjB1bmkwMUY0dW5pMDFGNUFyaW5nYWN1dGVhcmluZ2Fj
dXRlQUVhY3V0ZWFlYWN1dGVPc2xhc2hhY3V0ZW9zbGFzaGFjdXRldW5pMDIwMHVuaTAyMDF1bmkwMjA0dW5pMDIwNXVuaTAyMDh1
bmkwMjA5dW5pMDIwQ3VuaTAyMER1bmkwMjEwdW5pMDIxMXVuaTAyMTR1bmkwMjE1dW5pMDIxOHVuaTAyMTl1bmkwMjFBdW5pMDIx
QnVuaTAyMzd1bmkwMjU4dW5pMDI1OXVuaTAyQkV1bmkwMkJGdW5pMDNBOXBpbWludXRlc2Vjb25kRXVyb3BhcnRpYWxkaWZmdW5p
MjIwNnByb2R1Y3RzdW1tYXRpb25yYWRpY2FsaW5maW5pdHlpbnRlZ3JhbGFwcHJveGVxdWFsbm90ZXF1YWxsZXNzZXF1YWxncmVh
dGVyZXF1YWxsb3plbmdldW5pMjY2RHVuaTI2NkV1bmkyNjZGZl9pZl9sTHNsYXNoLjAwMWxzbGFzaC4wMDFTY2Fyb24uMDAxc2Nh
cm9uLjAwMVpjYXJvbi4wMDF6Y2Fyb24uMDAxVmVyc2lvbiAwLjkwNUNvcHlyaWdodCBcKGNcKSAyMDI1LCBTdGVpbmJlcmcgTWVk
aWEgVGVjaG5vbG9naWVzIEdtYkggXChodHRwOi8vd3d3LnN0ZWluYmVyZy5uZXQvXCksIHdpdGggUmVzZXJ2ZWQgRm9udCBOYW1l
ICJBY2FkZW1pY28iLgoKVGhpcyBGb250IFNvZnR3YXJlIGlzIGxpY2Vuc2VkIHVuZGVyIHRoZSBTSUwgT3BlbiBGb250IExpY2Vu
c2UsIFZlcnNpb24gMS4xLiBUaGlzIGxpY2Vuc2UgaXMgY29waWVkIGJlbG93LCBhbmQgaXMgYWxzbyBhdmFpbGFibGUgd2l0aCBh
IEZBUSBhdDogaHR0cDovL3NjcmlwdHMuc2lsLm9yZy9PRkwKCi0tLS0tLS0tLS0tLS0tLS0tLS0tLS0tLS0tLS0tLS0tLS0tLS0t
LS0tLS0tLS0tLS0tLS0tLS0tLS0tClNJTCBPUEVOIEZPTlQgTElDRU5TRSBWZXJzaW9uIDEuMSAtIDI2IEZlYnJ1YXJ5IDIwMDcK
LS0tLS0tLS0tLS0tLS0tLS0tLS0tLS0tLS0tLS0tLS0tLS0tLS0tLS0tLS0tLS0tLS0tLS0tLS0tLS0KClBSRUFNQkxFClRoZSBn
b2FscyBvZiB0aGUgT3BlbiBGb250IExpY2Vuc2UgXChPRkxcKSBhcmUgdG8gc3RpbXVsYXRlIHdvcmxkd2lkZSBkZXZlbG9wbWVu
dCBvZiBjb2xsYWJvcmF0aXZlIGZvbnQgcHJvamVjdHMsIHRvIHN1cHBvcnQgdGhlIGZvbnQgY3JlYXRpb24gZWZmb3J0cyBvZiBh
Y2FkZW1pYyBhbmQgbGluZ3Vpc3RpYyBjb21tdW5pdGllcywgYW5kIHRvIHByb3ZpZGUgYSBmcmVlIGFuZCBvcGVuIGZyYW1ld29y
ayBpbiB3aGljaCBmb250cyBtYXkgYmUgc2hhcmVkIGFuZCBpbXByb3ZlZCBpbiBwYXJ0bmVyc2hpcCB3aXRoIG90aGVycy4KClRo
ZSBPRkwgYWxsb3dzIHRoZSBsaWNlbnNlZCBmb250cyB0byBiZSB1c2VkLCBzdHVkaWVkLCBtb2RpZmllZCBhbmQgcmVkaXN0cmli
dXRlZCBmcmVlbHkgYXMgbG9uZyBhcyB0aGV5IGFyZSBub3Qgc29sZCBieSB0aGVtc2VsdmVzLiBUaGUgZm9udHMsIGluY2x1ZGlu
ZyBhbnkgZGVyaXZhdGl2ZSB3b3JrcywgY2FuIGJlIGJ1bmRsZWQsIGVtYmVkZGVkLCByZWRpc3RyaWJ1dGVkIGFuZC9vciBzb2xk
IHdpdGggYW55IHNvZnR3YXJlIHByb3ZpZGVkIHRoYXQgYW55IHJlc2VydmVkIG5hbWVzIGFyZSBub3QgdXNlZCBieSBkZXJpdmF0
aXZlIHdvcmtzLiBUaGUgZm9udHMgYW5kIGRlcml2YXRpdmVzLCBob3dldmVyLCBjYW5ub3QgYmUgcmVsZWFzZWQgdW5kZXIgYW55
IG90aGVyIHR5cGUgb2YgbGljZW5zZS4gVGhlIHJlcXVpcmVtZW50IGZvciBmb250cyB0byByZW1haW4gdW5kZXIgdGhpcyBsaWNl
bnNlIGRvZXMgbm90IGFwcGx5IHRvIGFueSBkb2N1bWVudCBjcmVhdGVkIHVzaW5nIHRoZSBmb250cyBvciB0aGVpciBkZXJpdmF0
aXZlcy4KCkRFRklOSVRJT05TCiJGb250IFNvZnR3YXJlIiByZWZlcnMgdG8gdGhlIHNldCBvZiBmaWxlcyByZWxlYXNlZCBieSB0
aGUgQ29weXJpZ2h0IEhvbGRlclwoc1wpIHVuZGVyIHRoaXMgbGljZW5zZSBhbmQgY2xlYXJseSBtYXJrZWQgYXMgc3VjaC4gVGhp
cyBtYXkKaW5jbHVkZSBzb3VyY2UgZmlsZXMsIGJ1aWxkIHNjcmlwdHMgYW5kIGRvY3VtZW50YXRpb24uCgoiUmVzZXJ2ZWQgRm9u
dCBOYW1lIiByZWZlcnMgdG8gYW55IG5hbWVzIHNwZWNpZmllZCBhcyBzdWNoIGFmdGVyIHRoZSBjb3B5cmlnaHQgc3RhdGVtZW50
XChzXCkuCgoiT3JpZ2luYWwgVmVyc2lvbiIgcmVmZXJzIHRvIHRoZSBjb2xsZWN0aW9uIG9mIEZvbnQgU29mdHdhcmUgY29tcG9u
ZW50cyBhcyBkaXN0cmlidXRlZCBieSB0aGUgQ29weXJpZ2h0IEhvbGRlclwoc1wpLgoKIk1vZGlmaWVkIFZlcnNpb24iIHJlZmVy
cyB0byBhbnkgZGVyaXZhdGl2ZSBtYWRlIGJ5IGFkZGluZyB0bywgZGVsZXRpbmcsIG9yIHN1YnN0aXR1dGluZyAtLSBpbiBwYXJ0
IG9yIGluIHdob2xlIC0tIGFueSBvZiB0aGUgY29tcG9uZW50cyBvZiB0aGUgT3JpZ2luYWwgVmVyc2lvbiwgYnkgY2hhbmdpbmcg
Zm9ybWF0cyBvciBieSBwb3J0aW5nIHRoZSBGb250IFNvZnR3YXJlIHRvIGEgbmV3IGVudmlyb25tZW50LgoKIkF1dGhvciIgcmVm
ZXJzIHRvIGFueSBkZXNpZ25lciwgZW5naW5lZXIsIHByb2dyYW1tZXIsIHRlY2huaWNhbCB3cml0ZXIgb3Igb3RoZXIgcGVyc29u
IHdobyBjb250cmlidXRlZCB0byB0aGUgRm9udCBTb2Z0d2FyZS4KClBFUk1JU1NJT04gJiBDT05ESVRJT05TClBlcm1pc3Npb24g
aXMgaGVyZWJ5IGdyYW50ZWQsIGZyZWUgb2YgY2hhcmdlLCB0byBhbnkgcGVyc29uIG9idGFpbmluZyBhIGNvcHkgb2YgdGhlIEZv
bnQgU29mdHdhcmUsIHRvIHVzZSwgc3R1ZHksIGNvcHksIG1lcmdlLCBlbWJlZCwgbW9kaWZ5LCByZWRpc3RyaWJ1dGUsIGFuZCBz
ZWxsIG1vZGlmaWVkIGFuZCB1bm1vZGlmaWVkIGNvcGllcyBvZiB0aGUgRm9udCBTb2Z0d2FyZSwgc3ViamVjdCB0byB0aGUgZm9s
bG93aW5nIGNvbmRpdGlvbnM6CgoxXCkgTmVpdGhlciB0aGUgRm9udCBTb2Z0d2FyZSBub3IgYW55IG9mIGl0cyBpbmRpdmlkdWFs
IGNvbXBvbmVudHMsIGluIE9yaWdpbmFsIG9yIE1vZGlmaWVkIFZlcnNpb25zLCBtYXkgYmUgc29sZCBieSBpdHNlbGYuCgoyXCkg
T3JpZ2luYWwgb3IgTW9kaWZpZWQgVmVyc2lvbnMgb2YgdGhlIEZvbnQgU29mdHdhcmUgbWF5IGJlIGJ1bmRsZWQsIHJlZGlzdHJp
YnV0ZWQgYW5kL29yIHNvbGQgd2l0aCBhbnkgc29mdHdhcmUsIHByb3ZpZGVkIHRoYXQgZWFjaCBjb3B5IGNvbnRhaW5zIHRoZSBh
Ym92ZSBjb3B5cmlnaHQgbm90aWNlIGFuZCB0aGlzIGxpY2Vuc2UuIFRoZXNlIGNhbiBiZSBpbmNsdWRlZCBlaXRoZXIgYXMgc3Rh
bmQtYWxvbmUgdGV4dCBmaWxlcywgaHVtYW4tcmVhZGFibGUgaGVhZGVycyBvciBpbiB0aGUgYXBwcm9wcmlhdGUgbWFjaGluZS1y
ZWFkYWJsZSBtZXRhZGF0YSBmaWVsZHMgd2l0aGluIHRleHQgb3IgYmluYXJ5IGZpbGVzIGFzIGxvbmcgYXMgdGhvc2UgZmllbGRz
IGNhbiBiZSBlYXNpbHkgdmlld2VkIGJ5IHRoZSB1c2VyLgoKM1wpIE5vIE1vZGlmaWVkIFZlcnNpb24gb2YgdGhlIEZvbnQgU29m
dHdhcmUgbWF5IHVzZSB0aGUgUmVzZXJ2ZWQgRm9udCBOYW1lXChzXCkgdW5sZXNzIGV4cGxpY2l0IHdyaXR0ZW4gcGVybWlzc2lv
biBpcyBncmFudGVkIGJ5IHRoZSBjb3JyZXNwb25kaW5nIENvcHlyaWdodCBIb2xkZXIuIFRoaXMgcmVzdHJpY3Rpb24gb25seSBh
cHBsaWVzIHRvIHRoZSBwcmltYXJ5IGZvbnQgbmFtZSBhcyBwcmVzZW50ZWQgdG8gdGhlIHVzZXJzLgoKNFwpIFRoZSBuYW1lXChz
XCkgb2YgdGhlIENvcHlyaWdodCBIb2xkZXJcKHNcKSBvciB0aGUgQXV0aG9yXChzXCkgb2YgdGhlIEZvbnQgU29mdHdhcmUgc2hh
bGwgbm90IGJlIHVzZWQgdG8gcHJvbW90ZSwgZW5kb3JzZSBvciBhZHZlcnRpc2UgYW55IE1vZGlmaWVkIFZlcnNpb24sIGV4Y2Vw
dCB0byBhY2tub3dsZWRnZSB0aGUgY29udHJpYnV0aW9uXChzXCkgb2YgdGhlIENvcHlyaWdodCBIb2xkZXJcKHNcKSBhbmQgdGhl
IEF1dGhvclwoc1wpIG9yIHdpdGggdGhlaXIgZXhwbGljaXQgd3JpdHRlbiBwZXJtaXNzaW9uLgoKNVwpIFRoZSBGb250IFNvZnR3
YXJlLCBtb2RpZmllZCBvciB1bm1vZGlmaWVkLCBpbiBwYXJ0IG9yIGluIHdob2xlLCBtdXN0IGJlIGRpc3RyaWJ1dGVkIGVudGly
ZWx5IHVuZGVyIHRoaXMgbGljZW5zZSwgYW5kIG11c3Qgbm90IGJlIGRpc3RyaWJ1dGVkIHVuZGVyIGFueSBvdGhlciBsaWNlbnNl
LiBUaGUgcmVxdWlyZW1lbnQgZm9yIGZvbnRzIHRvIHJlbWFpbiB1bmRlciB0aGlzIGxpY2Vuc2UgZG9lcyBub3QgYXBwbHkgdG8g
YW55IGRvY3VtZW50IGNyZWF0ZWQgdXNpbmcgdGhlIEZvbnQgU29mdHdhcmUuCgpURVJNSU5BVElPTgpUaGlzIGxpY2Vuc2UgYmVj
b21lcyBudWxsIGFuZCB2b2lkIGlmIGFueSBvZiB0aGUgYWJvdmUgY29uZGl0aW9ucyBhcmUgbm90IG1ldC4KCkRJU0NMQUlNRVIK
VEhFIEZPTlQgU09GVFdBUkUgSVMgUFJPVklERUQgIkFTIElTIiwgV0lUSE9VVCBXQVJSQU5UWSBPRiBBTlkgS0lORCwgRVhQUkVT
UyBPUiBJTVBMSUVELCBJTkNMVURJTkcgQlVUIE5PVCBMSU1JVEVEIFRPIEFOWSBXQVJSQU5USUVTIE9GIE1FUkNIQU5UQUJJTElU
WSwgRklUTkVTUyBGT1IgQSBQQVJUSUNVTEFSIFBVUlBPU0UgQU5EIE5PTklORlJJTkdFTUVOVCBPRiBDT1BZUklHSFQsIFBBVEVO
VCwgVFJBREVNQVJLLCBPUiBPVEhFUiBSSUdIVC4gSU4gTk8gRVZFTlQgU0hBTEwgVEhFIENPUFlSSUdIVCBIT0xERVIgQkUgTElB
QkxFIEZPUiBBTlkgQ0xBSU0sIERBTUFHRVMgT1IgT1RIRVIgTElBQklMSVRZLCBJTkNMVURJTkcgQU5ZIEdFTkVSQUwsIFNQRUNJ
QUwsIElORElSRUNULCBJTkNJREVOVEFMLCBPUiBDT05TRVFVRU5USUFMIERBTUFHRVMsIFdIRVRIRVIgSU4gQU4gQUNUSU9OIE9G
IENPTlRSQUNULCBUT1JUIE9SIE9USEVSV0lTRSwgQVJJU0lORyBGUk9NLCBPVVQgT0YgVEhFIFVTRSBPUiBJTkFCSUxJVFkgVE8g
VVNFIFRIRSBGT05UIFNPRlRXQVJFIE9SIEZST00gT1RIRVIgREVBTElOR1MgSU4gVEhFIEZPTlQgU09GVFdBUkUuQWNhZGVtaWNv
Tm9ybWFsAMgCAAEAHwAiACYAKgAvADMAQgBLAFIAWQBgAGYAawBwAHUAeQCpAL8AyADQANYBBgEPASoBPQFEAUwBTwFzAYEBrAG+
AccBywHOAdQB+wIXAhwCMwJJAl0CagJ1AuYC6wLvAzEDOQNyA6cDuQPLA9sD3wPoA+8D9gP+BAMECQQQBBUEjQSoBM0E1ATeBS8F
YwWmBbEF6QXyBfYF+gYjBnAGdwadBqMGzgbmBvsHFAcgBzkHRwdVB2kHdQd6B4QHjgedB6YHrwe8B8QHzAfUB9oH4Ah0CPYJdAnk
CfEKWQpdCmQKygseCzwLaAtsC9IL6gv2DFIMXwxoDL4MyAzQDNcM3QznDO8NIg1ODY8Nmg2jDawNtA3YDe0OJQ5bDmkOgw6xDsIO
yA7xDxkPJA8nD0sPbw+TD7QP1A/0EBMQJBA/EFgQchCDEJEQpxC8ENAQ4xD0EQMRDREdESIRLBE6EUcRVBFhEW4ReRGFEYsRlhGh
EawRsxG9EccR0RHaEeMR7BH1Ef4SBxIQEhkSIhIoEi4SMxI4FfcL+0AFi9gjHYv3CywdYSMdi/sI+wkvHfsHLR0ORR0O8uzyC4uL
HgvAicASC7j3Dguh+D0VuQaklHh3H/uFBwuLrvdcufhidwtcXGFNgR8ObH13d2cbC4R8r/g6rwuuuli3Gwv3QC8dC/cJix4L9xP3
AQuLHosLt+sVOtlt0czEqL22Hl6jo2nAG56Mu5mYpHmkGISAe4N/G3Z3pp4f974HziusPx4LQPsQaytqnW+vq6GaraNzmYyhH3gd
C4ux99Gz97ysC/ejfbH5N7ELcFK+XhsLvgOb+UcVlbqLlRudoXx3H/x9B/sl9yVm9xj3G/ca1vcpHvgRB9awpcweq/uath0LmTb3
MI4Fvx0L47y47x9vBleFbWNBG0Jts7+FH28GJ7xe4x4OSklPTR5WiFixvhr34Qf7OYAFCxWMoIuMGwv7IkL7CfsWCxU8HYoxPklJ
6YC2tsGwsJsfbKF0b3CAd4gZd4hgk7AasKHHtqYeDil/+2dl+xoa65QVVB0LsbAVZvfgsDcHd4CemR/40Qe3rI+jHsWq++Bszgaj
oYZgH/zRB31/eHoeC6n7W6v3ONhWdvc3q/eJvWCrC45rL4sfk4cFCwElHQvQBw73EQOhHQsVbqF1qKiioaiodKJubnV0bh73XBZu
oXWoqKKhqKh0om5udXRuHgsVioq+jIsa9yHmBZqToJ2eGpl+nnRwf355eR4LJh1LHQtz6/smgAVvB6iJw4ZgGvvOB3WDfHMeC7L4
MBXIqcrR0alKTk5xSkRBbsrMHgvc9wWQw7znikNC+wh5Vlgxl80eC2F3ZHNXGlS3d7h6Hgs0zknfz8G5urceC+4DuPf6FftZ9xD7
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
DT0NQA1DDZANnw3mDfAOiQ6MDo8Osg7CDuQPCw8dDykPLA9XD6cPug+9D9EP1A/ZD+oQABB9EIARGhEdESARjxH8Ef8SAhJEEkcS
lRKfEzMTQRNEE5ITqBP3FC8UexSSFWgV5xa+Fs0XfBgHGD0YYBlQGV8ZlxnAGcsaFRqBGqIaxhr+GxEbYxvPHJwdAR0JHRAdGx1M
HWYdeh1/HaAdqB2wHbwd0x3aHeEd7B4CHn4eqx6zHroexR7aHuse9B8WHzYfQR9TH1of0SBvIHcgfiCJIL4g3yDrIO4hFiEdISQh
RyFdIX8hhiGrIc8iLyJeImUibCKPIqIiuSLfIuYi7iL1IxgjLSNDI3gjnSOnI7EjxCPwJAskiCSQJJkkpSSwJMwk3iTpJPQlAiU2
JUslaSV0JX8lmSWvJcMl0yXzJgcmEiYdJikmNCZHJoMmlibKJucnHSctJzonTSe2J8cn2CfiJ+wn/ygTKC4oUShdKGAohCirKLgo
wylLKdcp3inlKf4qGyooKkkqdSqeKs4q/SsFKw0rKytGK1IraSvlLDosRCxOLGEseiyqLLstSC2eLaQtqy3OLe0uDS4cLiQuKy43
LkIuny8SLx0vJy9GL2YveS+cL9YwDTAdMDswTjBqMIAwojDdMSAxOTFsMZUxvzHLMewyDTItMkwyXDKcMqcyrjK8MyozqjQkNHk0
1zUzNVM1ajV0NX41iDWSNZ01pzXENd818TYcNis2TzZRNlw2ZjaANqw2tja+NsU23jbuNvc2/jcONxw3IzdHN1E3XTdnN3c3ijeS
N5s3sTe7N8w39DgXOC44SjhVOKo4rDj/OVI5YTlwOYI5kjmiObE52TnpOmU64zr0OwY7EDsgOzA7Yzt7O5M8BTy6PNw8/z1GPVI9
Yj1uPX09mD4sPug/cT/pQB1Ae0DCQPtBZkG+QdlCCEIuQlZCi0M2Q7JFAEUCRQRFBkUIRShFPkVIRVJFdEV7+3kO/I8O+3kO+3kO
+2d99w75CHcS4fcOPLQT4OG6FWmmcK2sp6atrG+namlwcGkeyPlFFWWKe25UGhPQVK/7cfsMGkoHi7QjHcwH9wyq93HCGsN7qWWK
Hg77CvlydwHI3/LfA/KZCvdPFpoKDrygdvdXx/dJxwGn+J0D9w73VxVj+1cFxga091YF9yoGY/tWBcgGtvdXBfctx/sjBrD3SQX1
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
NSpHtPQeE9ik+BgV18yw0uHAYzAejVBmV1N4P6QgpYrsCA68fa73hMD3+q8StPM96/eL7xPszu8VOOVs0vdn0vdj90f3LlX3SvtN
HhP0+x8wIPsZ+wrVMvcPH9GJyrOywor7O277NvsphwgT7HlZj6gfoaGZohqsdqJqYnRuYx4T9Nn4GBXapvTu7LIlOThkMCsob+Xf
Hg77eXz3DveS9w4B2PcOA9j4OlYd/AwEdR0O+3l/9wstdvgF9w4S0PcOZ7kTqNf7RBXEos/ryhq8dr9UZXV0ZW2fb6seE2iVlI+V
G5SLgYVYUllncR8TcJL40VYdDu6WdgG96wO993EV+Lr7ewXVB/xa91L4WvdQBdQH/Lr7egUO7vcLy/dDzAG9+LoDvfdLFUv4ussH
/Lr3hBVK+LrMBw7ulnYB+IzrA/js97EV/Lr3egVCB/ha+1D8WvtSBUEH+Lr3ewUOTHz3DvjmrxKo1qz3DkGl8OsT7PdN91YVpQa0
kMSqqh73BvcGBa+ulru8GvEpzS41JVUrYqFlt7GcorEeq12Uqhq1yp2r1bJHSfsf+ypeovtRHhP0W/soVh0O93p7vfcgt1/H96i0
9yC5EoPz1+L3KcZ3pfdFvRPfQIP37RX7ZPc++y33Z/ct9yzl9yu5HmIG+xZLK077Jxv7WDf3DfdQ91j09yz3Yfcj8Dr7JjVl+zT7
EnGRp6KSH9n3owVKBn5lBa+Bc5hpG/s3RftFIl6pWcDKwMyzsB8puYSg9yDg9zL3DfdE+w33APtF+3H7UftD+20e959XFdLS9ybb
HhO+wLGKaW5ETPsiMmmJqqcfDj4KDoux98+197quEvce9wD3pfcIOvcLE/RKCvgfB/cJ9xjN9xT3DDOqIq8fE/jbudaY9wUa6TfY
Kx78PmjOBp2Ko392GvzkB4Fze4Me9yD30BX3RgaMl4iKjx8T9NV2slM/GjphPi8e+yIGf3eXmB/m+QcVE/j113n7DVJ8SlBzH3mE
eoiLGvs496IGn7GPlh6NqIyWGw6RHQ5eHfkekx0OPQoOPAr30rH3vqoB9yH290etA0oK9+6wLAd6fKGaH/et2QfYips2k08IrffY
bAaIiAUmgWVnKBtr96IGmZqZmR73GwbSvl9Opx9wl541jBurBoD3jQX83mzYBpSKpYJ8GvzzB4N7fYMeDosdDmYK97J1Cg5pHQ62
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
BsfGcVFqH/sX+34Fi42L+0r3tR6cgbCXoxu+qfu/bQayo4Zhph/3WvvGBQ77BfsrqPnOrBKkw3DpMM73EupHynDDE9LBVRVF1HDF
5su+5x6Jv3axbLIIE8mzsba3xBrtQrxJyx6Al1TAgZcIeqB+oqYawrmpvR6kiqqLcRoTzH15f391GnCheqSkop2n2k+qRTdBTTNb
omSnZR6Cg2Zmg4MIE+J0cIVoaRo+umLDWB6ShMlXkoMIq260aFsaVVlqWX5gkKAeE9KdppSlGqZ7nXFoenRqHhPhpvgnFbCkpqeg
HrByrGqsbQipb7llXBqKcW9ecIB7l0PJfJkIaqljrLoaDvtC+O3yAZsiHQOb+SAiCvfafMrZpPg1pdjMEoHL89f3np2GnvclyxP9
gIH3/BX7ZPc7+ztbHfc89ztbHfs89zz7ZPtk+zv7PPtkHsuKFfdA9x/3IPdA90D3IPsg5h37IPsf+0D7QPsf9x/3QB7zghX7Ddsk
9xHTxK/Oph6SnZGinxp4Bj12ak4yG/sAb/cC5eCa9xj3BOGoPEWjHxP+gIuNhYwengaE90cFdgZ0ZAWjaWWcYRv7FET7FvsGHw77
Qfgso3Op9xSh7KMSh8tcw/cYxRO6h/hvFVq/ebm3sJ2pqB5wm5t2rhuYq5Sakx9/mgUTdoeEgIaDG31+nJYf90oHtEufWVk5d1F3
l3qjoJqUoB6Ze5SYGqKNto2cG6O5fm8fUwcTukqD+yB0ORrLkRW3saC1lB6ZjqqSm4wIUQdiVmhjbXmipR4OOr736gGz+BauHfdc
FoeIi4iPhwhTyur7BZkbk46PlpZc2VzOH7nNu9qWGpaFj4R9TjY9LB4O7vfVzAH4dc0DvffVFYv4QyUKi/tpLx3NJQqL96qLHvyF
Bg73enzK9rZpoPdHo/c8nuvMEoPL91nJ9yvKp5v1yxPf4IP3/BX7ZPc7+ztbHfc89ztbHfs89zz7ZPtk+zv7PPtkHsuKFfdA9x/3
IPdA90D3IPsg5h37IPsf+0D7QPsf9x/3QB73l5AVwQaVmISHkx9iz0r7MfIbv5rBtx97BoqHiXeKhwiCiYR5fxuAgpmViB9y44Cy
aJdplhm2kqGIqKEIl5OemsAawF67VR77hni3BpWWg38f+98HE7/ggIOCfx5edvdToFsGgoSSlx++9/MVybGAQ2eAcWh9H4eDeId+
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
5cCAHRPpoGwdE9qgagr3X5MVQB2TmaKMlhuconpvb3h2YnVjm5ODH35xBXmksH6hG9TCpsHBb6Jaf26Bi4udzYsfi2SLjh4OX/tq
rOmqtLJ9dqN2+FC2g3cSwMH3NdChxxPdwPcKpxUT5cC3HRPbwKcKE93Adh0T5cCBHRPdwGMK9w6WFUAdk5mijJYbnKJ6b294dmJ1
Y5uTgx9+cQV5pLB+oRvUwqbBwW+iWn9ugYuLnc2LH4tki44eDuy4CtNLCsX6ViAdex3VYR2D+VggHfc0+2Ws6aq+vAqB0BP4Zh3D
axVAHZOZooyWGxP0ax37CuQdvLz4DrsS7eForePQhKwT+W8dE/ZfCvdO/DiOCjwK+SOpysIB96f2A2YdQPosIB37DoO9+A6790z3
CxLt4Wit9xG9cqwT8m8dE+xfCvfo95JbCiQK4yQd9w/1+Bm+E+xrCpW6i5Ubigr3eeMVjKCLjBsT3C0KE+wrHRPcLAoT7CkdE9xw
Ur5eGxPsKB0pCuAkHfHg93zeE7ZGHRN2Nh0Ttjgd9w3rFYygi4wbE24tChN2Kx0TbiwKE3YpHRNuNB0TdigdJAryUAr3f/IV983C
+80GDikK78IS8eD3fN4TfCYdE7yMCvcT9wMV983C+80GDiQK1MAB9w/1tDgK1DUd+BzUMAopCtHAEvHgeDgKc94TeSYdE7mkHRN2
97DcFTcdJArEr/cTsDsK2SYK9wM1Hfe39zFDCikKwSYKEvHgnSYKmd4Tv4BGHRN/gDYdE7+AOB33S/c5QwpPCvfVzBWKiqwrCubh
BZWTmJydGpiDnXx6g396fx6y+xcVioqsKwrm4QWVk5icnRqYg518eoN/en8eDvODOQoTuCYdZx33N9QVioqsKwrl5gWUk5mdnhqZ
gp59eYR+eX8esvseFYqKqysK5eYFlZOYnZ4amYOefHqDfnmAHg73yPtrwfcnwvkeqzsKy+H3gzUd+AT9Yjsd8/trwfctxFut+Bq2
EvHg90Dhcd4T2kYdmTb3MI4FE7qcCh5WiFixvhr34WgK+ED8WDsd+G6RdvlVq/dDwnQK9x3FFYv3By0di/cILgq1JQr7CywdPiMd
+wsvCg73o5V2+FOr9z/CeQr3cvcKFYv3By0di/cILgq1JQr7CywdPiMd+wsvCg6DHfdDwpYdZPl7IAqoCvc/whKP5DP3Lfc991QT
2ncKE7ZyHRPawB33KfkfIAqDHcXyEvdU8pT1efKs9z0T+podOPmuFTYKE/b3XBY2Cg6lHfuE3BWKir4rCvch5gWak6CdnhqZfp50
cH9+eXkeDqYdbOcVioq+Kwr3IeYFmpOgnZ4amX6edHB/fnl5Hg5ZHdrwAfeT8FId+0X3OigKtQrf8AH3Y/AD99/4QRX7tfwaBWT4
HAeW90kFawZae3ouRRv7Ngb3t/gaBa78Bgd/+zcFrwa5l5vdzBug9z0oClkdzKcd+633piAdjQo/950gHZ0K+CgH9wSO9wvtHpUK
Mh0B93an90X3AQP4z7AVg3SblR/47geZo5eWHsqs/NEGfPuFBasGoeSk9wL3BpQI9zQGl5t9fx/7ojsHQYHovX4fb/vjpwaUyZ7e
2pII0fu8BoJ5f4Ue+zQGM03g2HgfetEFawaa+6IF+OawBg73BPtfsfjDsvecsgGL9wn4DvUD9034RRVk9wUHeTEF/Cs6XE1xG4V4
jJYfk5uSoRqkdKhsWX5lcFircsv3Jr33Ave/yB6d55fDk7MI9xSy+w0Glr6MkprICPWipLKlG5CSiIaMH49+doB8GmehfKeynKWp
rW+6UfsEYln7kVMeDjMdEiUd+B33Eif3ERPouPf+FftR9wv7T/difx3uZe1L0R6bk5yWmp0IE/Cfo5SjnxqhgZ17mB6Wfn2RfRt8
e4R8fx+Bf4V8fRp/kH+XgB6YgZ2IfxqHiYWFhB5/fQXAUUGtNqUKHhPo902k+1X7IoQd+0tx91z3IB8OKh0Srej3Z/cCRucT6KYK
2XLRWrgeE/CroJ6pqBqrcKtqcHRzc32Xbp6CHo2Dh4aGhgidbGWVXxs6HR/ojBXenC4dHhPo9wWY+w02XR37AHv3GdofDiQKEvcP
9fgZvoX3AhPwawrOBqMK+FcHE+jAmr6zvBqrcKtqcHRzc32Xbp6CHogHE/B/e4GChh6k+zRrpgfPmWJFH/wEB/sLJlciOCe66x74
bQejm5SejB7Yq/vZBg7zgzkKlO8TeCYdE7hLHRN4tAqrB21SkbMf99kHE3y7msi0thqoc6htcnZ1dX+WcJyDHhO4jYBxfX6GCKUH
+zWABWu1B6GZfXIf+2gHSklPTR5WiFixvhr34WgKDicdw00K+TIE9wsvCovYJQr3CywdYSUK+wguCvsHLR0ONwq2wmAKE/QwHRPs
MR0T9D0dbfjhIB00CrlqHT/6GyAdMwrBlgpD+SYgHTMdsVIKuvjbIB0qHbZTCnD4YSAdJArOUAr3h/eDIB0pCs2ACuz3jSAdJArZ
8jsKsyIduTUd95H3FRU2CvdcFjYK+zTwIR0pCt3yEvHgRiIdiZwd9zX3fEUdE3b7W/t2IgokCtrywMKYHfcWRB37XfepIB0pCujy
u8IS8eBGIh2J3hO8gEYdE3yANh0TvIA4HRN7AOv3L0Qd+1/3pCAdJArS8pgd9w5EHUz3hiMKKQrb8hLx4EAiHY/eE7tGHRN7Nh0T
uzgdE3fl9yJEHTz3dCMKlx1ICrONHfcu+OMgHT8dtIcdVvgFIB33o/trwfcosPk3sUEd9wbh929DHfdh+/s7HYT7acH3JK/4Oq8B
rejU4ejnA633fBV+HfcdQPcC+yc6HR7ojF0K9zj7djsdVx3Bnx3D+cwgHYsd93P4PSEdbAqh92MhHScdxCYKAYP3KvcLJgpACr/4
67MdWvcgIR3GHaMmCnJxCrGvHVr3CCEd+M2IHXL4lyEdbQr7pd4hHfeHnwr3qPmoRR38AfzIcgrLHfcd+KZFHfuB/EiPHT4Ktvkf
IQrPfLP4M7JgChPoMB0T2DEdE+gpf/tnZfsaGuuUFVQdl/jBIQr3Oj0K9zD6EyEKjXxaHWMd+wX3cSEKLGkKUB2B+hMhCvtGhh0B
9wrgAzEKd/kaIQr3j32x+TexASUd+DdDHeD4zCEKhaAdmvhVIQr3gF8dMveIIQpji674HrZjs/ePdwFkCgNlHbP5JSEK97N/Cve8
92UhCvcDgzkKE7gmHWcd9yr3ayEK9w/7MfcDqsodtuyrb9ET00BYChPLgIAdE9NAbB0TtUBqCvdX+9EnCl/7MfcDqtMd9zG2v8cT
124dE8+nChPXiQoTt2MK9wL7zicK9zT7K/cDs7wKbrYT8GYdqPv4FRPoNQr7Cvsn9wOnvdsdxba8rBP2bx0T7l8K9yj9cycKVx0B
NfPU3ANwHQ4yCgGw6/d97QP4ZPd5FfcTPPcP+x77KU77CPsaHvfdBilzJ/sNRVe6x2oea3oFN7XWV+cb9x7e9wb3Fh/7cPduFeqp
JTwf+2MGfnyamIof0p/d5h4Olx37MPgqtfdovAG36erUA/c1+VkVYWh8QWEfr3qNjo2OjY4ZqJ6Xnrcb1YtNYUdpY197eYueH5ic
hK8ap3CTeXN1e2qIHlnKY7vvvtLg3ljKLYweDvsw+Cq892i1AbXU6ukD90/4KhW1rprVtR9nnImIiYiJiBlueH94XxtBi8m1z62z
t5udi3gffnqSZxpvpoOdo6GbrI4evUyzWydYRDY4vkzpih4O+0L5E8IBlffPA7/4niAK+0L4nsIBlffPA5X5SiAd+0L4rsABpKf3
b6cD9zf4rjAK+0L47/AB9wjwA/cI+SEoCvtC+J4mCgHNJgoDzfkCQwr7QvtrwQHc4QP3QJAVPB37Qvi9JB2M99kToIz4vTkdE2At
ChOgKx0TYCwKE6ApHRNgNB0ToCgdgh2D+DkDg/imRR3H+x4hHffLh9pA2vjerxL3DPb4BvcDE3j3gdoVLFyF53sfbYal+zQF93UG
lJoFPvcbhvbkGvcWp/dR9zH3N6H7TPsbM337B0H7GB4TuJR8Bfd1BqX3NG2QBS97XJEsG38GzM7V6fcAGvdL+xD3QvtF+0sj+0T7
SR4TeCK+MM1GHg73Sn7G9+LOqXcB92+29w7tA8L4ChWLoG+LHovOrNceiPtDifsKJz+mchiLr56eph6eprrN93saoweL9xeNix6L
gvszMxozoVDhwK6ssaUefJ97dnd4b5cZapl/s66ukPc1tBrZjQWmqZGeshpqlgWEb2WJixr7zQYsUkKLHw6891vQAYv4vwP3oARG
+L9CHfiB91vQAYv6fgP3oARG+n5CHfvD1R0DpPi7tB37w/hsd/c61x0D9zz5FFsK+8N79wsB9wq9A/c8kRVECvsK1R33Kr0DpPi7
tR33XBZdpVi/r6Gkr75jkmF2yPcKp7wefZ11goaGgoQZWWFgVUYaDvsK+Gx39zrXHfcqvQP4BPkUiwr7XBZECvsKePcLAfcKvfcq
vQP4BI4VXAr7XBZECoT4g6b3aXcS95Wod6AT0Pez+xcVi5T3+6zTHhPgZb6G0tQa4R2fn6iKH6mNdtkdibEFxa+xqRqpd59uih5t
jXd2bW2vZVEaZWUHUWWvbRttdndtjR9uip93qamxr8UbsQZChkRlWB4T0KxDnvtz+xwaDoTZpvgapvdpdwH3lagD92r3wBWxWJBE
QhplBlFlr20bbXd3bowfbYmgd6mpsa/FG7FlBlFnZW0abZ92qY0eqIqfn6mpZ7HFGo2xBeEdoJ+piR+ojHfZHdSQ0rG+HmW+htLU
GrEGxbFnqRupn5+oih+pjXafbW1lZ1EbZQaJsQXFr7GpGql3n26KHm2Nd3Ztba9lURplZQdRZa9tG212d22NH26Kn3epqbGvxRux
BkKGRGVYHg7u90n3/QH3Dvf9A/cO9/0VJ9s77+/c2+/vOtwnJzs6Jx4O98x89xEB1fcR9yj3Efco9xEUcNW6FVMd96UWUx33pRZT
HQ749oekfHb39qR5pPd9psWkErfS93Wt0dL3dqiZ0vd2qBPv8PhghAoT3/DBHRPv8JMKE9/wdx35LPv2rAoT7/DPHdePFbwdDvun
+XF3Aan3QJQKDiL5cXcBqffflAr3MxayHQ77jL736gGz906uHQ77jL736gGy904D93KwHQ776JF2AftX+MED+yB8FfiK+WQFVAb8
iv1kBQ68fbb3ibnEutD3OpivEtn3B/sA9wUT7N33phX7K53T+x33PRv3E4rE4J73CAhtBjBva0kmG/sedfct5x/3RgahuQX7XMT3
RgaiugUT6vtYBuKk9zX3DOuzJD+nHhP8qwZ992oFcgZ5ZH50gqV6kxkT6p9lcJRgG/s4Vvsg+xxqH4mIhYseE+xZBnhcBcxSXQZ5
XQUO+IH3zaD4Bpx7mxL3Rcf3f6X3vsgTvPcD9+IVdvdSoFoHgYaVkh/3yweqkZehzqE4V5MenwaD9ysF++AGgfsrBZ8Gv5Wf3s8b
oo9+bR/7yweBg4SEHveLihV39y6fB22NaJKtGvfRB/cj/BAFnwb3G/gUBfvuB4R/gYUeXXb3TqBfBoZ/k5If9+cHE9yVmZGSHpGn
i5EbnPsfB/sF+9H7DffRBfscegaRp4uRG5OKmoZ/Gvu9B2VtfWqHHg73noKofXb3u6fvp/dgoxL3Bsv3sLxutfc9tXS2E/5Akgr7
E/zuFT7YaM7dzrrhzHGkUqUeE/2AsKalpbkazkupUEdNYENRonq5bh4T/kBSb2x0ikwIvI8Vuq+ptZseunnXgUgaT1VyVk9pocwe
E/2AmPd3Fbq7pq60uHhTZ25saH8eX5pOkMcaDqd9sfgTwfedwAHI4vez2gP4kPfuFfdJpkX3kPtJG0lshWBNH4B5nmeogwilq8Kr
uRv3IYKX+2d1+yIIxGVjs0YbIy4t+w95H/shdtb7CfcQG/c41/dV9zulH/sC+xMVM31YIDEbL3/x5pkf5piu7usb5KUuLH0fDvcX
i7gBrfiiA/jEFouLpS8d+4/5QS8dXXyLHov7ef0yix5xB/d5+NUVi/dM/KiLHvv5Bg73TTOw+WOqAfcB8/eg8wP4PPkwFaOsh18f
/RIHfYB4dx5VZveksFUGen+emR/5Ege2oZCjHrCq/RZssAajoYZgH/0SB31/eHoeVWb3pLBVBneAnpkf+RIHt6yPox4OvC7b+Tqs
Aaf4nQP3z/fpFftI99gF91oG9wyaTjKhH6qTgfdDBfx3agb3YvwX+2L74gVm+IwHnPd0cZAF+x9meoE0G/usBg65+HB3Aav4yQOr
+C8Vi5Zlix7bqwWL92T8xi8duJ+LHov3cfqTLx1mlIsei/tW/fgvHfs8+FWLHg73jPcSxfdgwwG6vfjCvQP4C/fhFcZeT788GztL
RDMzy0Tb0dW10LMfQMe9Ztcb28vS4+NL0js8WVpOUh9sVhVPY2pnORtYYrnDw7S5vt2gaEK/H8iPFbiuusXXG760XVNTYl1YRWun
1FMfDvsR+1+1+krCEvch3U7kE9D3rPngFTRAQfwsqB/8WatzRW5ukMJoG252em5zq3Cs9wTV9w/34XYfE+B29+GNSob3Cgj3CoaO
q6iojmKrG5+hm6qwVpd0Hw6p9xvCncewwp3HAbH4XwP4YvhGqx1o+x2rHQ73I/cLy/dDzAG9+LoDvfdLFUv4ussH/Lr3hBVK+LrM
B/wi/G8VwQb3TPkKBVYGDq0Kxvg0Ffi2+3EF0gf8V/dK+Ff3SAXQB/y2+28Fg/vXFUb4wkIdrQr48fhyFfy2928FRgf4V/tI/Ff7
SgVEB/i293EF/L77mRVG+MJCHYtCyvlC0AG8+C4D979CFfc0+Cz7NPguBTMG+zb8Lvc0/CwFufmBFfce++j7H/vu+x/37gUOO5N2
+DHai3cBs9b3NPMD9wL3FBWLh+XHGqOMnY2RHpGdsqyglwiTmJmOlxuamIWAlB+ae5RxbxpwhGt5bB53Z2BbXm4IiIWGiocbfYia
kh9X+xkVhY+QiY8bkI+Oix+4pa+zsaUI9xnouubQGuFJwUaPHoCBioiAH3uGeYV6gQiDgnt+gxuIiouMiB+AkIWVlhqNrJT3/Kka
m32UfHZzfHCKHouR/eyXfB4O+2M2+gIBs7v3DrsD4/glFZ3arauSj4mGHvsaB3RBbWuChI6QHvcb99IViYmKihuLOG1pg4aMkR73
bQeUg5GDHnsGgYWFgh/9MgeDj4i6Co2LjIwek57TqrEbmJSHgR/7VgeCkoWUHpwGk5KRlB/5IQeRho+GioiLiooeDiAl+h8B9LL3
BrK+mwP3lve4FXGETXFuG4OEjY+KH4iQiqiqGrOMuY6VHqGOxqesG5STiIaNH46EjmtoGmiIZoiAHuX3ZxWUj5KWkhroB5GHj4aI
iouKiB6LcYCFih6BgpKVH/czB5KEkoB+g4SEHvs9B4p+h3p/g3yCX3l1hQh/h5uVH/cwB5OCkoJ+g4SDHvtDB3mDfoOHHoSHcYGL
GoGIhYGDGi4HhI+Hugqek5SQHoyNjIwblJN+gR/7FQd9hH+Ehx6DiXB/ixqBiYWAgxovB4OPh5EejY2NjRuLnZKWjx6NjYyLjBuU
knyFH/s0B4OThZSYlJGTHvdJB5yRlJKNHtqsBY2NjIwblpF7hB/7NweDk4WUmpKRkx73TQeVkZuUjx6Uj6aVixqUj5KVkxrnB5KH
j4aIiouJiB5pfgWDgpObH/cNB5SSo5WPHg6KHYwdih2MHfc0i7L5IKoB9yj1A6j3vxU3B/f495IF2Qf78fySjwoOrwqk99MVIwf3
lPeSBe0H+5T8qHQdDrEKzUsKxvpQIB17HdJhHYX5VSAdWR3Apx37r/eaFfcLLwqL2CUK9wssHWElCvsILgr7By0dDo0KKfedIB18
mvholveJngb7W5IHsArgC6uQDAzLoJaTnQwN+WYU+I8VrxMAnwIAAQAbACMAJgBCAEcASwBQAFMAZgBvAHcAewCEAIsAkACUAJcA
nwCkAKkArQDPAOEA6ADtAPoBAQEGAQsBEAEdAUMBTQF2AXwBfwGCAZgBpAG3AcIBzAHRAfEB9QIBAg4CEwIXAhsCHwIjAjQCOQI9
Am0CnAKjAskCzALvAvMDBQMTAxwDJgMvAzYDPgNGA04DVgNcA2IDaANtA+gEVASvBLMEwwTUBSwFSwW5Bb0GJQZcBpwHAgcHBxcH
JQd4B30HggeQB+YH6gfzCDAINgg7CHsIgAiFCJUImQikCKsItgjFCMsI5QjtCQkJEgk9CUYJXQmHCY0JsQnVCd4J/goaCigKPApU
ClsKcwp9CooKjwqZCqMKsgq6CsgKzArZCt4K6Ar0CvkLBQsQCxcLHgsoCzILPAtFC04LVwtgC2YLaxWL9wctHYv3CC4KtSUK+wss
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
95P1A5D3NxWBCgsB7d33e9wDoK4VaPeGrgd0jFGFsxr3agfOzM3OvLtfWB77lAd3fIJ1iR5eaPeOsFIGfH2dmB+K934F9wdTyTBG
YXJKVR738KsK/NMHZlKOd4oeC3wdgwoL5R2ZHQvCEvHg93zeE7wmHYwKC/sC60jx4Mqm2bYepbqMv7wa+DQHn52boh7DqvvWbNUG
pJ98dR/8QgdmiWWFch5Ke2RsSBtWQ6jKlY2dlIyMi4qNH4GemomXG62in761bK5fSGxOUB8LwpsdCwH3GLj4WoYKC/dGrArPHTX4
UBV8p56IpBulno+isR/76f0aBbcG+Bj5ZAVfBml2UGNZG1l2m6B8H6h9cJxeGyU8KzFqHwvrE/lRHQu1A4cKC6OtFakK+Fv87wW0
+PQGxbmyvh6r+4hrB8G+ZE0f/EEH/Eb4xgX7QWsGoIqwjJ56CJSCoXWKGvyUB1NMbF6DHgt6HUIKC3YdgR0Lowr4EQfWsKXMHqv7
mrYdCxVcCgtLHRN8Nh0TvDgdC7UKxcKqHQsVQB2TmaKMlhtrHbgd+N7FHfzaB3t5c3oeC7kdngoeCzkdE9gtChPoKx0T2CwKE+gp
HRPYNB0T6CgdmAqD+9ezCgu8Hfwk9/IVu53E9wHTG495qHWjf5FkeF2BcAgLA/dF+WsVsh0Lpoqcgn59a4hnGm6ge6azl6euzVOq
Tvsyd/tA+wmIHj1h2fv2Bnl/fHseDsIB9wrgAzEKC09qV1xFG/sNc+/tH/fdBvcaTvcI+ykLs/fIFW/3cKdLB4V/lJUf+BFpB2tu
YH9gG3PPB5STh4Af+74Hg4GAgh4L+XIVmgoLa4F1dnaW+zaOdh93joh0pxuphp6hjh+Oopb3M6Mao4Geax4L9xrW9xH3D/cNUvcK
+xxOZG9gXx/35gf7Pn8FawepiMKHYBoLvx0T3EpJT00L+0KLsPgXtfeOsgHv4PcF7wOdsBVm97CwOQd3fKacHwu/al2pThv7F0X7
EvsLH+6UFdiY9wjw7az7BDoLfbH5N7EBJR34N/cRAwvenC4d9wWY+w02XR37AHv3GdoeCxWKiqsrCuPlBZSTmJyeGpmDnn16hH55
C/cs+btHCg6doXx3H/x9B/sl9yVm9xj3G/ca1vcpHgt/97QFagZmTQULG/tj+wv7TftSH9IdC+cdfh0Lffc3BXkGZ2sFC6n7W7X4
4a9rqwtp96StB1STS6LOGvhcBwvaHeD3DDTgCwf7QXwFbwepiciKXRoLFdAdC/cs4dD313cBvvjCAwv7MrMKC/tUi675IoUdAwvV
ULD3z7X3uq5rqwv3D7gKCzxv+xImI3/3FdceCxXCBviK+WQFVAYLmTb3MI4FC3GLsvgargu8fbX29yj4LKoL+0L7AZj5yJgBC3yy
gHb5V7GEdwsSg/cq+yr5dAuRHo2NjI0biwuv+Cy293OrAQuw+SOpEven9guAfJibHwt9BWgHCwAAAAAAABIA3gABAAAAAAABAAkA
AAABAAAAAAACAAcACQABAAAAAAAEAAkAEAABAAAAAAAFAA0AGQABAAAAAAAGAAkAJgADAAEECQAAIoQALwADAAEECQABABIiswAD
AAEECQACAA4ixQADAAEECQADAE4i0wADAAEECQAEABIjIQADAAEECQAFABojMwADAAEECQAGABIjTQADAAEECQAIAEIjXwADAAEE
CQAKAQ4joQADAAEECQALADIkrwADAAEECQAMADIk4QADAAEECQANIoQlEwADAAEECQAOADRHl0FjYWRlbWljb1JlZ3VsYXJBY2Fk
ZW1pY29WZXJzaW9uIDAuOTA1QWNhZGVtaWNvAEMAbwBwAHkAcgBpAGcAaAB0ACAAqQAgADIAMAAyADUALAAgAFMAdABlAGkAbgBi
AGUAcgBnACAATQBlAGQAaQBhACAAVABlAGMAaABuAG8AbABvAGcAaQBlAHMAIABHAG0AYgBIACAAKABoAHQAdABwADoALwAvAHcA
dwB3AC4AcwB0AGUAaQBuAGIAZQByAGcALgBuAGUAdAAvACkALAAgAHcAaQB0AGgAIABSAGUAcwBlAHIAdgBlAGQAIABGAG8AbgB0
ACAATgBhAG0AZQAgACIAQQBjAGEAZABlAG0AaQBjAG8AIgAuAAoACgBUAGgAaQBzACAARgBvAG4AdAAgAFMAbwBmAHQAdwBhAHIA
ZQAgAGkAcwAgAGwAaQBjAGUAbgBzAGUAZAAgAHUAbgBkAGUAcgAgAHQAaABlACAAUwBJAEwAIABPAHAAZQBuACAARgBvAG4AdAAg
AEwAaQBjAGUAbgBzAGUALAAgAFYAZQByAHMAaQBvAG4AIAAxAC4AMQAuACAAVABoAGkAcwAgAGwAaQBjAGUAbgBzAGUAIABpAHMA
IABjAG8AcABpAGUAZAAgAGIAZQBsAG8AdwAsACAAYQBuAGQAIABpAHMAIABhAGwAcwBvACAAYQB2AGEAaQBsAGEAYgBsAGUAIAB3
AGkAdABoACAAYQAgAEYAQQBRACAAYQB0ADoAIABoAHQAdABwADoALwAvAHMAYwByAGkAcAB0AHMALgBzAGkAbAAuAG8AcgBnAC8A
TwBGAEwACgAKAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAt
AC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAKAFMASQBMACAATwBQAEUATgAgAEYA
TwBOAFQAIABMAEkAQwBFAE4AUwBFACAAVgBlAHIAcwBpAG8AbgAgADEALgAxACAALQAgADIANgAgAEYAZQBiAHIAdQBhAHIAeQAg
ADIAMAAwADcACgAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0A
LQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ACgAKAFAAUgBFAEEATQBCAEwARQAK
AFQAaABlACAAZwBvAGEAbABzACAAbwBmACAAdABoAGUAIABPAHAAZQBuACAARgBvAG4AdAAgAEwAaQBjAGUAbgBzAGUAIAAoAE8A
RgBMACkAIABhAHIAZQAgAHQAbwAgAHMAdABpAG0AdQBsAGEAdABlACAAdwBvAHIAbABkAHcAaQBkAGUAIABkAGUAdgBlAGwAbwBw
AG0AZQBuAHQAIABvAGYAIABjAG8AbABsAGEAYgBvAHIAYQB0AGkAdgBlACAAZgBvAG4AdAAgAHAAcgBvAGoAZQBjAHQAcwAsACAA
dABvACAAcwB1AHAAcABvAHIAdAAgAHQAaABlACAAZgBvAG4AdAAgAGMAcgBlAGEAdABpAG8AbgAgAGUAZgBmAG8AcgB0AHMAIABv
AGYAIABhAGMAYQBkAGUAbQBpAGMAIABhAG4AZAAgAGwAaQBuAGcAdQBpAHMAdABpAGMAIABjAG8AbQBtAHUAbgBpAHQAaQBlAHMA
LAAgAGEAbgBkACAAdABvACAAcAByAG8AdgBpAGQAZQAgAGEAIABmAHIAZQBlACAAYQBuAGQAIABvAHAAZQBuACAAZgByAGEAbQBl
AHcAbwByAGsAIABpAG4AIAB3AGgAaQBjAGgAIABmAG8AbgB0AHMAIABtAGEAeQAgAGIAZQAgAHMAaABhAHIAZQBkACAAYQBuAGQA
IABpAG0AcAByAG8AdgBlAGQAIABpAG4AIABwAGEAcgB0AG4AZQByAHMAaABpAHAAIAB3AGkAdABoACAAbwB0AGgAZQByAHMALgAK
AAoAVABoAGUAIABPAEYATAAgAGEAbABsAG8AdwBzACAAdABoAGUAIABsAGkAYwBlAG4AcwBlAGQAIABmAG8AbgB0AHMAIAB0AG8A
IABiAGUAIAB1AHMAZQBkACwAIABzAHQAdQBkAGkAZQBkACwAIABtAG8AZABpAGYAaQBlAGQAIABhAG4AZAAgAHIAZQBkAGkAcwB0
AHIAaQBiAHUAdABlAGQAIABmAHIAZQBlAGwAeQAgAGEAcwAgAGwAbwBuAGcAIABhAHMAIAB0AGgAZQB5ACAAYQByAGUAIABuAG8A
dAAgAHMAbwBsAGQAIABiAHkAIAB0AGgAZQBtAHMAZQBsAHYAZQBzAC4AIABUAGgAZQAgAGYAbwBuAHQAcwAsACAAaQBuAGMAbAB1
AGQAaQBuAGcAIABhAG4AeQAgAGQAZQByAGkAdgBhAHQAaQB2AGUAIAB3AG8AcgBrAHMALAAgAGMAYQBuACAAYgBlACAAYgB1AG4A
ZABsAGUAZAAsACAAZQBtAGIAZQBkAGQAZQBkACwAIAByAGUAZABpAHMAdAByAGkAYgB1AHQAZQBkACAAYQBuAGQALwBvAHIAIABz
AG8AbABkACAAdwBpAHQAaAAgAGEAbgB5ACAAcwBvAGYAdAB3AGEAcgBlACAAcAByAG8AdgBpAGQAZQBkACAAdABoAGEAdAAgAGEA
bgB5ACAAcgBlAHMAZQByAHYAZQBkACAAbgBhAG0AZQBzACAAYQByAGUAIABuAG8AdAAgAHUAcwBlAGQAIABiAHkAIABkAGUAcgBp
AHYAYQB0AGkAdgBlACAAdwBvAHIAawBzAC4AIABUAGgAZQAgAGYAbwBuAHQAcwAgAGEAbgBkACAAZABlAHIAaQB2AGEAdABpAHYA
ZQBzACwAIABoAG8AdwBlAHYAZQByACwAIABjAGEAbgBuAG8AdAAgAGIAZQAgAHIAZQBsAGUAYQBzAGUAZAAgAHUAbgBkAGUAcgAg
AGEAbgB5ACAAbwB0AGgAZQByACAAdAB5AHAAZQAgAG8AZgAgAGwAaQBjAGUAbgBzAGUALgAgAFQAaABlACAAcgBlAHEAdQBpAHIA
ZQBtAGUAbgB0ACAAZgBvAHIAIABmAG8AbgB0AHMAIAB0AG8AIAByAGUAbQBhAGkAbgAgAHUAbgBkAGUAcgAgAHQAaABpAHMAIABs
AGkAYwBlAG4AcwBlACAAZABvAGUAcwAgAG4AbwB0ACAAYQBwAHAAbAB5ACAAdABvACAAYQBuAHkAIABkAG8AYwB1AG0AZQBuAHQA
IABjAHIAZQBhAHQAZQBkACAAdQBzAGkAbgBnACAAdABoAGUAIABmAG8AbgB0AHMAIABvAHIAIAB0AGgAZQBpAHIAIABkAGUAcgBp
AHYAYQB0AGkAdgBlAHMALgAKAAoARABFAEYASQBOAEkAVABJAE8ATgBTAAoAIgBGAG8AbgB0ACAAUwBvAGYAdAB3AGEAcgBlACIA
IAByAGUAZgBlAHIAcwAgAHQAbwAgAHQAaABlACAAcwBlAHQAIABvAGYAIABmAGkAbABlAHMAIAByAGUAbABlAGEAcwBlAGQAIABi
AHkAIAB0AGgAZQAgAEMAbwBwAHkAcgBpAGcAaAB0ACAASABvAGwAZABlAHIAKABzACkAIAB1AG4AZABlAHIAIAB0AGgAaQBzACAA
bABpAGMAZQBuAHMAZQAgAGEAbgBkACAAYwBsAGUAYQByAGwAeQAgAG0AYQByAGsAZQBkACAAYQBzACAAcwB1AGMAaAAuACAAVABo
AGkAcwAgAG0AYQB5AAoAaQBuAGMAbAB1AGQAZQAgAHMAbwB1AHIAYwBlACAAZgBpAGwAZQBzACwAIABiAHUAaQBsAGQAIABzAGMA
cgBpAHAAdABzACAAYQBuAGQAIABkAG8AYwB1AG0AZQBuAHQAYQB0AGkAbwBuAC4ACgAKACIAUgBlAHMAZQByAHYAZQBkACAARgBv
AG4AdAAgAE4AYQBtAGUAIgAgAHIAZQBmAGUAcgBzACAAdABvACAAYQBuAHkAIABuAGEAbQBlAHMAIABzAHAAZQBjAGkAZgBpAGUA
ZAAgAGEAcwAgAHMAdQBjAGgAIABhAGYAdABlAHIAIAB0AGgAZQAgAGMAbwBwAHkAcgBpAGcAaAB0ACAAcwB0AGEAdABlAG0AZQBu
AHQAKABzACkALgAKAAoAIgBPAHIAaQBnAGkAbgBhAGwAIABWAGUAcgBzAGkAbwBuACIAIAByAGUAZgBlAHIAcwAgAHQAbwAgAHQA
aABlACAAYwBvAGwAbABlAGMAdABpAG8AbgAgAG8AZgAgAEYAbwBuAHQAIABTAG8AZgB0AHcAYQByAGUAIABjAG8AbQBwAG8AbgBl
AG4AdABzACAAYQBzACAAZABpAHMAdAByAGkAYgB1AHQAZQBkACAAYgB5ACAAdABoAGUAIABDAG8AcAB5AHIAaQBnAGgAdAAgAEgA
bwBsAGQAZQByACgAcwApAC4ACgAKACIATQBvAGQAaQBmAGkAZQBkACAAVgBlAHIAcwBpAG8AbgAiACAAcgBlAGYAZQByAHMAIAB0
AG8AIABhAG4AeQAgAGQAZQByAGkAdgBhAHQAaQB2AGUAIABtAGEAZABlACAAYgB5ACAAYQBkAGQAaQBuAGcAIAB0AG8ALAAgAGQA
ZQBsAGUAdABpAG4AZwAsACAAbwByACAAcwB1AGIAcwB0AGkAdAB1AHQAaQBuAGcAIAAtAC0AIABpAG4AIABwAGEAcgB0ACAAbwBy
ACAAaQBuACAAdwBoAG8AbABlACAALQAtACAAYQBuAHkAIABvAGYAIAB0AGgAZQAgAGMAbwBtAHAAbwBuAGUAbgB0AHMAIABvAGYA
IAB0AGgAZQAgAE8AcgBpAGcAaQBuAGEAbAAgAFYAZQByAHMAaQBvAG4ALAAgAGIAeQAgAGMAaABhAG4AZwBpAG4AZwAgAGYAbwBy
AG0AYQB0AHMAIABvAHIAIABiAHkAIABwAG8AcgB0AGkAbgBnACAAdABoAGUAIABGAG8AbgB0ACAAUwBvAGYAdAB3AGEAcgBlACAA
dABvACAAYQAgAG4AZQB3ACAAZQBuAHYAaQByAG8AbgBtAGUAbgB0AC4ACgAKACIAQQB1AHQAaABvAHIAIgAgAHIAZQBmAGUAcgBz
ACAAdABvACAAYQBuAHkAIABkAGUAcwBpAGcAbgBlAHIALAAgAGUAbgBnAGkAbgBlAGUAcgAsACAAcAByAG8AZwByAGEAbQBtAGUA
cgAsACAAdABlAGMAaABuAGkAYwBhAGwAIAB3AHIAaQB0AGUAcgAgAG8AcgAgAG8AdABoAGUAcgAgAHAAZQByAHMAbwBuACAAdwBo
AG8AIABjAG8AbgB0AHIAaQBiAHUAdABlAGQAIAB0AG8AIAB0AGgAZQAgAEYAbwBuAHQAIABTAG8AZgB0AHcAYQByAGUALgAKAAoA
UABFAFIATQBJAFMAUwBJAE8ATgAgACYAIABDAE8ATgBEAEkAVABJAE8ATgBTAAoAUABlAHIAbQBpAHMAcwBpAG8AbgAgAGkAcwAg
AGgAZQByAGUAYgB5ACAAZwByAGEAbgB0AGUAZAAsACAAZgByAGUAZQAgAG8AZgAgAGMAaABhAHIAZwBlACwAIAB0AG8AIABhAG4A
eQAgAHAAZQByAHMAbwBuACAAbwBiAHQAYQBpAG4AaQBuAGcAIABhACAAYwBvAHAAeQAgAG8AZgAgAHQAaABlACAARgBvAG4AdAAg
AFMAbwBmAHQAdwBhAHIAZQAsACAAdABvACAAdQBzAGUALAAgAHMAdAB1AGQAeQAsACAAYwBvAHAAeQAsACAAbQBlAHIAZwBlACwA
IABlAG0AYgBlAGQALAAgAG0AbwBkAGkAZgB5ACwAIAByAGUAZABpAHMAdAByAGkAYgB1AHQAZQAsACAAYQBuAGQAIABzAGUAbABs
ACAAbQBvAGQAaQBmAGkAZQBkACAAYQBuAGQAIAB1AG4AbQBvAGQAaQBmAGkAZQBkACAAYwBvAHAAaQBlAHMAIABvAGYAIAB0AGgA
ZQAgAEYAbwBuAHQAIABTAG8AZgB0AHcAYQByAGUALAAgAHMAdQBiAGoAZQBjAHQAIAB0AG8AIAB0AGgAZQAgAGYAbwBsAGwAbwB3
AGkAbgBnACAAYwBvAG4AZABpAHQAaQBvAG4AcwA6AAoACgAxACkAIABOAGUAaQB0AGgAZQByACAAdABoAGUAIABGAG8AbgB0ACAA
UwBvAGYAdAB3AGEAcgBlACAAbgBvAHIAIABhAG4AeQAgAG8AZgAgAGkAdABzACAAaQBuAGQAaQB2AGkAZAB1AGEAbAAgAGMAbwBt
AHAAbwBuAGUAbgB0AHMALAAgAGkAbgAgAE8AcgBpAGcAaQBuAGEAbAAgAG8AcgAgAE0AbwBkAGkAZgBpAGUAZAAgAFYAZQByAHMA
aQBvAG4AcwAsACAAbQBhAHkAIABiAGUAIABzAG8AbABkACAAYgB5ACAAaQB0AHMAZQBsAGYALgAKAAoAMgApACAATwByAGkAZwBp
AG4AYQBsACAAbwByACAATQBvAGQAaQBmAGkAZQBkACAAVgBlAHIAcwBpAG8AbgBzACAAbwBmACAAdABoAGUAIABGAG8AbgB0ACAA
UwBvAGYAdAB3AGEAcgBlACAAbQBhAHkAIABiAGUAIABiAHUAbgBkAGwAZQBkACwAIAByAGUAZABpAHMAdAByAGkAYgB1AHQAZQBk
ACAAYQBuAGQALwBvAHIAIABzAG8AbABkACAAdwBpAHQAaAAgAGEAbgB5ACAAcwBvAGYAdAB3AGEAcgBlACwAIABwAHIAbwB2AGkA
ZABlAGQAIAB0AGgAYQB0ACAAZQBhAGMAaAAgAGMAbwBwAHkAIABjAG8AbgB0AGEAaQBuAHMAIAB0AGgAZQAgAGEAYgBvAHYAZQAg
AGMAbwBwAHkAcgBpAGcAaAB0ACAAbgBvAHQAaQBjAGUAIABhAG4AZAAgAHQAaABpAHMAIABsAGkAYwBlAG4AcwBlAC4AIABUAGgA
ZQBzAGUAIABjAGEAbgAgAGIAZQAgAGkAbgBjAGwAdQBkAGUAZAAgAGUAaQB0AGgAZQByACAAYQBzACAAcwB0AGEAbgBkAC0AYQBs
AG8AbgBlACAAdABlAHgAdAAgAGYAaQBsAGUAcwAsACAAaAB1AG0AYQBuAC0AcgBlAGEAZABhAGIAbABlACAAaABlAGEAZABlAHIA
cwAgAG8AcgAgAGkAbgAgAHQAaABlACAAYQBwAHAAcgBvAHAAcgBpAGEAdABlACAAbQBhAGMAaABpAG4AZQAtAHIAZQBhAGQAYQBi
AGwAZQAgAG0AZQB0AGEAZABhAHQAYQAgAGYAaQBlAGwAZABzACAAdwBpAHQAaABpAG4AIAB0AGUAeAB0ACAAbwByACAAYgBpAG4A
YQByAHkAIABmAGkAbABlAHMAIABhAHMAIABsAG8AbgBnACAAYQBzACAAdABoAG8AcwBlACAAZgBpAGUAbABkAHMAIABjAGEAbgAg
AGIAZQAgAGUAYQBzAGkAbAB5ACAAdgBpAGUAdwBlAGQAIABiAHkAIAB0AGgAZQAgAHUAcwBlAHIALgAKAAoAMwApACAATgBvACAA
TQBvAGQAaQBmAGkAZQBkACAAVgBlAHIAcwBpAG8AbgAgAG8AZgAgAHQAaABlACAARgBvAG4AdAAgAFMAbwBmAHQAdwBhAHIAZQAg
AG0AYQB5ACAAdQBzAGUAIAB0AGgAZQAgAFIAZQBzAGUAcgB2AGUAZAAgAEYAbwBuAHQAIABOAGEAbQBlACgAcwApACAAdQBuAGwA
ZQBzAHMAIABlAHgAcABsAGkAYwBpAHQAIAB3AHIAaQB0AHQAZQBuACAAcABlAHIAbQBpAHMAcwBpAG8AbgAgAGkAcwAgAGcAcgBh
AG4AdABlAGQAIABiAHkAIAB0AGgAZQAgAGMAbwByAHIAZQBzAHAAbwBuAGQAaQBuAGcAIABDAG8AcAB5AHIAaQBnAGgAdAAgAEgA
bwBsAGQAZQByAC4AIABUAGgAaQBzACAAcgBlAHMAdAByAGkAYwB0AGkAbwBuACAAbwBuAGwAeQAgAGEAcABwAGwAaQBlAHMAIAB0
AG8AIAB0AGgAZQAgAHAAcgBpAG0AYQByAHkAIABmAG8AbgB0ACAAbgBhAG0AZQAgAGEAcwAgAHAAcgBlAHMAZQBuAHQAZQBkACAA
dABvACAAdABoAGUAIAB1AHMAZQByAHMALgAKAAoANAApACAAVABoAGUAIABuAGEAbQBlACgAcwApACAAbwBmACAAdABoAGUAIABD
AG8AcAB5AHIAaQBnAGgAdAAgAEgAbwBsAGQAZQByACgAcwApACAAbwByACAAdABoAGUAIABBAHUAdABoAG8AcgAoAHMAKQAgAG8A
ZgAgAHQAaABlACAARgBvAG4AdAAgAFMAbwBmAHQAdwBhAHIAZQAgAHMAaABhAGwAbAAgAG4AbwB0ACAAYgBlACAAdQBzAGUAZAAg
AHQAbwAgAHAAcgBvAG0AbwB0AGUALAAgAGUAbgBkAG8AcgBzAGUAIABvAHIAIABhAGQAdgBlAHIAdABpAHMAZQAgAGEAbgB5ACAA
TQBvAGQAaQBmAGkAZQBkACAAVgBlAHIAcwBpAG8AbgAsACAAZQB4AGMAZQBwAHQAIAB0AG8AIABhAGMAawBuAG8AdwBsAGUAZABn
AGUAIAB0AGgAZQAgAGMAbwBuAHQAcgBpAGIAdQB0AGkAbwBuACgAcwApACAAbwBmACAAdABoAGUAIABDAG8AcAB5AHIAaQBnAGgA
dAAgAEgAbwBsAGQAZQByACgAcwApACAAYQBuAGQAIAB0AGgAZQAgAEEAdQB0AGgAbwByACgAcwApACAAbwByACAAdwBpAHQAaAAg
AHQAaABlAGkAcgAgAGUAeABwAGwAaQBjAGkAdAAgAHcAcgBpAHQAdABlAG4AIABwAGUAcgBtAGkAcwBzAGkAbwBuAC4ACgAKADUA
KQAgAFQAaABlACAARgBvAG4AdAAgAFMAbwBmAHQAdwBhAHIAZQAsACAAbQBvAGQAaQBmAGkAZQBkACAAbwByACAAdQBuAG0AbwBk
AGkAZgBpAGUAZAAsACAAaQBuACAAcABhAHIAdAAgAG8AcgAgAGkAbgAgAHcAaABvAGwAZQAsACAAbQB1AHMAdAAgAGIAZQAgAGQA
aQBzAHQAcgBpAGIAdQB0AGUAZAAgAGUAbgB0AGkAcgBlAGwAeQAgAHUAbgBkAGUAcgAgAHQAaABpAHMAIABsAGkAYwBlAG4AcwBl
ACwAIABhAG4AZAAgAG0AdQBzAHQAIABuAG8AdAAgAGIAZQAgAGQAaQBzAHQAcgBpAGIAdQB0AGUAZAAgAHUAbgBkAGUAcgAgAGEA
bgB5ACAAbwB0AGgAZQByACAAbABpAGMAZQBuAHMAZQAuACAAVABoAGUAIAByAGUAcQB1AGkAcgBlAG0AZQBuAHQAIABmAG8AcgAg
AGYAbwBuAHQAcwAgAHQAbwAgAHIAZQBtAGEAaQBuACAAdQBuAGQAZQByACAAdABoAGkAcwAgAGwAaQBjAGUAbgBzAGUAIABkAG8A
ZQBzACAAbgBvAHQAIABhAHAAcABsAHkAIAB0AG8AIABhAG4AeQAgAGQAbwBjAHUAbQBlAG4AdAAgAGMAcgBlAGEAdABlAGQAIAB1
AHMAaQBuAGcAIAB0AGgAZQAgAEYAbwBuAHQAIABTAG8AZgB0AHcAYQByAGUALgAKAAoAVABFAFIATQBJAE4AQQBUAEkATwBOAAoA
VABoAGkAcwAgAGwAaQBjAGUAbgBzAGUAIABiAGUAYwBvAG0AZQBzACAAbgB1AGwAbAAgAGEAbgBkACAAdgBvAGkAZAAgAGkAZgAg
AGEAbgB5ACAAbwBmACAAdABoAGUAIABhAGIAbwB2AGUAIABjAG8AbgBkAGkAdABpAG8AbgBzACAAYQByAGUAIABuAG8AdAAgAG0A
ZQB0AC4ACgAKAEQASQBTAEMATABBAEkATQBFAFIACgBUAEgARQAgAEYATwBOAFQAIABTAE8ARgBUAFcAQQBSAEUAIABJAFMAIABQ
AFIATwBWAEkARABFAEQAIAAiAEEAUwAgAEkAUwAiACwAIABXAEkAVABIAE8AVQBUACAAVwBBAFIAUgBBAE4AVABZACAATwBGACAA
QQBOAFkAIABLAEkATgBEACwAIABFAFgAUABSAEUAUwBTACAATwBSACAASQBNAFAATABJAEUARAAsACAASQBOAEMATABVAEQASQBO
AEcAIABCAFUAVAAgAE4ATwBUACAATABJAE0ASQBUAEUARAAgAFQATwAgAEEATgBZACAAVwBBAFIAUgBBAE4AVABJAEUAUwAgAE8A
RgAgAE0ARQBSAEMASABBAE4AVABBAEIASQBMAEkAVABZACwAIABGAEkAVABOAEUAUwBTACAARgBPAFIAIABBACAAUABBAFIAVABJ
AEMAVQBMAEEAUgAgAFAAVQBSAFAATwBTAEUAIABBAE4ARAAgAE4ATwBOAEkATgBGAFIASQBOAEcARQBNAEUATgBUACAATwBGACAA
QwBPAFAAWQBSAEkARwBIAFQALAAgAFAAQQBUAEUATgBUACwAIABUAFIAQQBEAEUATQBBAFIASwAsACAATwBSACAATwBUAEgARQBS
ACAAUgBJAEcASABUAC4AIABJAE4AIABOAE8AIABFAFYARQBOAFQAIABTAEgAQQBMAEwAIABUAEgARQAgAEMATwBQAFkAUgBJAEcA
SABUACAASABPAEwARABFAFIAIABCAEUAIABMAEkAQQBCAEwARQAgAEYATwBSACAAQQBOAFkAIABDAEwAQQBJAE0ALAAgAEQAQQBN
AEEARwBFAFMAIABPAFIAIABPAFQASABFAFIAIABMAEkAQQBCAEkATABJAFQAWQAsACAASQBOAEMATABVAEQASQBOAEcAIABBAE4A
WQAgAEcARQBOAEUAUgBBAEwALAAgAFMAUABFAEMASQBBAEwALAAgAEkATgBEAEkAUgBFAEMAVAAsACAASQBOAEMASQBEAEUATgBU
AEEATAAsACAATwBSACAAQwBPAE4AUwBFAFEAVQBFAE4AVABJAEEATAAgAEQAQQBNAEEARwBFAFMALAAgAFcASABFAFQASABFAFIA
IABJAE4AIABBAE4AIABBAEMAVABJAE8ATgAgAE8ARgAgAEMATwBOAFQAUgBBAEMAVAAsACAAVABPAFIAVAAgAE8AUgAgAE8AVABI
AEUAUgBXAEkAUwBFACwAIABBAFIASQBTAEkATgBHACAARgBSAE8ATQAsACAATwBVAFQAIABPAEYAIABUAEgARQAgAFUAUwBFACAA
TwBSACAASQBOAEEAQgBJAEwASQBUAFkAIABUAE8AIABVAFMARQAgAFQASABFACAARgBPAE4AVAAgAFMATwBGAFQAVwBBAFIARQAg
AE8AUgAgAEYAUgBPAE0AIABPAFQASABFAFIAIABEAEUAQQBMAEkATgBHAFMAIABJAE4AIABUAEgARQAgAEYATwBOAFQAIABTAE8A
RgBUAFcAQQBSAEUALgBBAGMAYQBkAGUAbQBpAGMAbwBSAGUAZwB1AGwAYQByAFYAZQByAHMAaQBvAG4AIAAwAC4AOQAwADUAOwBT
AE0AVABHADsAQQBjAGEAZABlAG0AaQBjAG8AOwAyADAAMgA1ADsARgBMADgANAAyAEEAYwBhAGQAZQBtAGkAYwBvAFYAZQByAHMA
aQBvAG4AIAAwAC4AOQAwADUAQQBjAGEAZABlAG0AaQBjAG8AUwB0AGUAaQBuAGIAZQByAGcAIABNAGUAZABpAGEAIABUAGUAYwBo
AG4AbwBsAG8AZwBpAGUAcwAgAEcAbQBiAEgAQwBvAHAAeQByAGkAZwBoAHQAIACpACAAMgAwADIANQAgAFMAdABlAGkAbgBiAGUA
cgBnACAATQBlAGQAaQBhACAAVABlAGMAaABuAG8AbABvAGcAaQBlAHMAIABHAG0AYgBIAC4AIABUAGgAaQBzACAAZgBvAG4AdAAg
AGkAcwAgAGwAaQBjAGUAbgBzAGUAZAAgAHUAbgBkAGUAcgAgAHQAaABlACAAUwBJAEwAIABPAHAAZQBuACAARgBvAG4AdAAgAEwA
aQBjAGUAbgBzAGUAIAAoAGgAdAB0AHAAOgAvAC8AcwBjAHIAaQBwAHQAcwAuAHMAaQBsAC4AbwByAGcALwBPAEYATAApAC4AaAB0
AHQAcAA6AC8ALwB3AHcAdwAuAHMAdABlAGkAbgBiAGUAcgBnAC4AbgBlAHQALwBoAHQAdABwADoALwAvAHcAdwB3AC4AcwB0AGUA
aQBuAGIAZQByAGcALgBuAGUAdAAvAEMAbwBwAHkAcgBpAGcAaAB0ACAAqQAgADIAMAAyADAALAAgAFMAdABlAGkAbgBiAGUAcgBn
ACAATQBlAGQAaQBhACAAVABlAGMAaABuAG8AbABvAGcAaQBlAHMAIABHAG0AYgBIACAAKABoAHQAdABwADoALwAvAHcAdwB3AC4A
cwB0AGUAaQBuAGIAZQByAGcALgBuAGUAdAAvACkALAAgAHcAaQB0AGgAIABSAGUAcwBlAHIAdgBlAGQAIABGAG8AbgB0ACAATgBh
AG0AZQAgACIAQQBjAGEAZABlAG0AaQBjAG8AIgAuAAoACgBUAGgAaQBzACAARgBvAG4AdAAgAFMAbwBmAHQAdwBhAHIAZQAgAGkA
cwAgAGwAaQBjAGUAbgBzAGUAZAAgAHUAbgBkAGUAcgAgAHQAaABlACAAUwBJAEwAIABPAHAAZQBuACAARgBvAG4AdAAgAEwAaQBj
AGUAbgBzAGUALAAgAFYAZQByAHMAaQBvAG4AIAAxAC4AMQAuACAAVABoAGkAcwAgAGwAaQBjAGUAbgBzAGUAIABpAHMAIABjAG8A
cABpAGUAZAAgAGIAZQBsAG8AdwAsACAAYQBuAGQAIABpAHMAIABhAGwAcwBvACAAYQB2AGEAaQBsAGEAYgBsAGUAIAB3AGkAdABo
ACAAYQAgAEYAQQBRACAAYQB0ADoAIABoAHQAdABwADoALwAvAHMAYwByAGkAcAB0AHMALgBzAGkAbAAuAG8AcgBnAC8ATwBGAEwA
CgAKAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAt
AC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAKAFMASQBMACAATwBQAEUATgAgAEYATwBOAFQA
IABMAEkAQwBFAE4AUwBFACAAVgBlAHIAcwBpAG8AbgAgADEALgAxACAALQAgADIANgAgAEYAZQBiAHIAdQBhAHIAeQAgADIAMAAw
ADcACgAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0A
LQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ACgAKAFAAUgBFAEEATQBCAEwARQAKAFQAaABl
ACAAZwBvAGEAbABzACAAbwBmACAAdABoAGUAIABPAHAAZQBuACAARgBvAG4AdAAgAEwAaQBjAGUAbgBzAGUAIAAoAE8ARgBMACkA
IABhAHIAZQAgAHQAbwAgAHMAdABpAG0AdQBsAGEAdABlACAAdwBvAHIAbABkAHcAaQBkAGUAIABkAGUAdgBlAGwAbwBwAG0AZQBu
AHQAIABvAGYAIABjAG8AbABsAGEAYgBvAHIAYQB0AGkAdgBlACAAZgBvAG4AdAAgAHAAcgBvAGoAZQBjAHQAcwAsACAAdABvACAA
cwB1AHAAcABvAHIAdAAgAHQAaABlACAAZgBvAG4AdAAgAGMAcgBlAGEAdABpAG8AbgAgAGUAZgBmAG8AcgB0AHMAIABvAGYAIABh
AGMAYQBkAGUAbQBpAGMAIABhAG4AZAAgAGwAaQBuAGcAdQBpAHMAdABpAGMAIABjAG8AbQBtAHUAbgBpAHQAaQBlAHMALAAgAGEA
bgBkACAAdABvACAAcAByAG8AdgBpAGQAZQAgAGEAIABmAHIAZQBlACAAYQBuAGQAIABvAHAAZQBuACAAZgByAGEAbQBlAHcAbwBy
AGsAIABpAG4AIAB3AGgAaQBjAGgAIABmAG8AbgB0AHMAIABtAGEAeQAgAGIAZQAgAHMAaABhAHIAZQBkACAAYQBuAGQAIABpAG0A
cAByAG8AdgBlAGQAIABpAG4AIABwAGEAcgB0AG4AZQByAHMAaABpAHAAIAB3AGkAdABoACAAbwB0AGgAZQByAHMALgAKAAoAVABo
AGUAIABPAEYATAAgAGEAbABsAG8AdwBzACAAdABoAGUAIABsAGkAYwBlAG4AcwBlAGQAIABmAG8AbgB0AHMAIAB0AG8AIABiAGUA
IAB1AHMAZQBkACwAIABzAHQAdQBkAGkAZQBkACwAIABtAG8AZABpAGYAaQBlAGQAIABhAG4AZAAgAHIAZQBkAGkAcwB0AHIAaQBi
AHUAdABlAGQAIABmAHIAZQBlAGwAeQAgAGEAcwAgAGwAbwBuAGcAIABhAHMAIAB0AGgAZQB5ACAAYQByAGUAIABuAG8AdAAgAHMA
bwBsAGQAIABiAHkAIAB0AGgAZQBtAHMAZQBsAHYAZQBzAC4AIABUAGgAZQAgAGYAbwBuAHQAcwAsACAAaQBuAGMAbAB1AGQAaQBu
AGcAIABhAG4AeQAgAGQAZQByAGkAdgBhAHQAaQB2AGUAIAB3AG8AcgBrAHMALAAgAGMAYQBuACAAYgBlACAAYgB1AG4AZABsAGUA
ZAAsACAAZQBtAGIAZQBkAGQAZQBkACwAIAByAGUAZABpAHMAdAByAGkAYgB1AHQAZQBkACAAYQBuAGQALwBvAHIAIABzAG8AbABk
ACAAdwBpAHQAaAAgAGEAbgB5ACAAcwBvAGYAdAB3AGEAcgBlACAAcAByAG8AdgBpAGQAZQBkACAAdABoAGEAdAAgAGEAbgB5ACAA
cgBlAHMAZQByAHYAZQBkACAAbgBhAG0AZQBzACAAYQByAGUAIABuAG8AdAAgAHUAcwBlAGQAIABiAHkAIABkAGUAcgBpAHYAYQB0
AGkAdgBlACAAdwBvAHIAawBzAC4AIABUAGgAZQAgAGYAbwBuAHQAcwAgAGEAbgBkACAAZABlAHIAaQB2AGEAdABpAHYAZQBzACwA
IABoAG8AdwBlAHYAZQByACwAIABjAGEAbgBuAG8AdAAgAGIAZQAgAHIAZQBsAGUAYQBzAGUAZAAgAHUAbgBkAGUAcgAgAGEAbgB5
ACAAbwB0AGgAZQByACAAdAB5AHAAZQAgAG8AZgAgAGwAaQBjAGUAbgBzAGUALgAgAFQAaABlACAAcgBlAHEAdQBpAHIAZQBtAGUA
bgB0ACAAZgBvAHIAIABmAG8AbgB0AHMAIAB0AG8AIAByAGUAbQBhAGkAbgAgAHUAbgBkAGUAcgAgAHQAaABpAHMAIABsAGkAYwBl
AG4AcwBlACAAZABvAGUAcwAgAG4AbwB0ACAAYQBwAHAAbAB5ACAAdABvACAAYQBuAHkAIABkAG8AYwB1AG0AZQBuAHQAIABjAHIA
ZQBhAHQAZQBkACAAdQBzAGkAbgBnACAAdABoAGUAIABmAG8AbgB0AHMAIABvAHIAIAB0AGgAZQBpAHIAIABkAGUAcgBpAHYAYQB0
AGkAdgBlAHMALgAKAAoARABFAEYASQBOAEkAVABJAE8ATgBTAAoAIgBGAG8AbgB0ACAAUwBvAGYAdAB3AGEAcgBlACIAIAByAGUA
ZgBlAHIAcwAgAHQAbwAgAHQAaABlACAAcwBlAHQAIABvAGYAIABmAGkAbABlAHMAIAByAGUAbABlAGEAcwBlAGQAIABiAHkAIAB0
AGgAZQAgAEMAbwBwAHkAcgBpAGcAaAB0ACAASABvAGwAZABlAHIAKABzACkAIAB1AG4AZABlAHIAIAB0AGgAaQBzACAAbABpAGMA
ZQBuAHMAZQAgAGEAbgBkACAAYwBsAGUAYQByAGwAeQAgAG0AYQByAGsAZQBkACAAYQBzACAAcwB1AGMAaAAuACAAVABoAGkAcwAg
AG0AYQB5AAoAaQBuAGMAbAB1AGQAZQAgAHMAbwB1AHIAYwBlACAAZgBpAGwAZQBzACwAIABiAHUAaQBsAGQAIABzAGMAcgBpAHAA
dABzACAAYQBuAGQAIABkAG8AYwB1AG0AZQBuAHQAYQB0AGkAbwBuAC4ACgAKACIAUgBlAHMAZQByAHYAZQBkACAARgBvAG4AdAAg
AE4AYQBtAGUAIgAgAHIAZQBmAGUAcgBzACAAdABvACAAYQBuAHkAIABuAGEAbQBlAHMAIABzAHAAZQBjAGkAZgBpAGUAZAAgAGEA
cwAgAHMAdQBjAGgAIABhAGYAdABlAHIAIAB0AGgAZQAgAGMAbwBwAHkAcgBpAGcAaAB0ACAAcwB0AGEAdABlAG0AZQBuAHQAKABz
ACkALgAKAAoAIgBPAHIAaQBnAGkAbgBhAGwAIABWAGUAcgBzAGkAbwBuACIAIAByAGUAZgBlAHIAcwAgAHQAbwAgAHQAaABlACAA
YwBvAGwAbABlAGMAdABpAG8AbgAgAG8AZgAgAEYAbwBuAHQAIABTAG8AZgB0AHcAYQByAGUAIABjAG8AbQBwAG8AbgBlAG4AdABz
ACAAYQBzACAAZABpAHMAdAByAGkAYgB1AHQAZQBkACAAYgB5ACAAdABoAGUAIABDAG8AcAB5AHIAaQBnAGgAdAAgAEgAbwBsAGQA
ZQByACgAcwApAC4ACgAKACIATQBvAGQAaQBmAGkAZQBkACAAVgBlAHIAcwBpAG8AbgAiACAAcgBlAGYAZQByAHMAIAB0AG8AIABh
AG4AeQAgAGQAZQByAGkAdgBhAHQAaQB2AGUAIABtAGEAZABlACAAYgB5ACAAYQBkAGQAaQBuAGcAIAB0AG8ALAAgAGQAZQBsAGUA
dABpAG4AZwAsACAAbwByACAAcwB1AGIAcwB0AGkAdAB1AHQAaQBuAGcAIAAtAC0AIABpAG4AIABwAGEAcgB0ACAAbwByACAAaQBu
ACAAdwBoAG8AbABlACAALQAtACAAYQBuAHkAIABvAGYAIAB0AGgAZQAgAGMAbwBtAHAAbwBuAGUAbgB0AHMAIABvAGYAIAB0AGgA
ZQAgAE8AcgBpAGcAaQBuAGEAbAAgAFYAZQByAHMAaQBvAG4ALAAgAGIAeQAgAGMAaABhAG4AZwBpAG4AZwAgAGYAbwByAG0AYQB0
AHMAIABvAHIAIABiAHkAIABwAG8AcgB0AGkAbgBnACAAdABoAGUAIABGAG8AbgB0ACAAUwBvAGYAdAB3AGEAcgBlACAAdABvACAA
YQAgAG4AZQB3ACAAZQBuAHYAaQByAG8AbgBtAGUAbgB0AC4ACgAKACIAQQB1AHQAaABvAHIAIgAgAHIAZQBmAGUAcgBzACAAdABv
ACAAYQBuAHkAIABkAGUAcwBpAGcAbgBlAHIALAAgAGUAbgBnAGkAbgBlAGUAcgAsACAAcAByAG8AZwByAGEAbQBtAGUAcgAsACAA
dABlAGMAaABuAGkAYwBhAGwAIAB3AHIAaQB0AGUAcgAgAG8AcgAgAG8AdABoAGUAcgAgAHAAZQByAHMAbwBuACAAdwBoAG8AIABj
AG8AbgB0AHIAaQBiAHUAdABlAGQAIAB0AG8AIAB0AGgAZQAgAEYAbwBuAHQAIABTAG8AZgB0AHcAYQByAGUALgAKAAoAUABFAFIA
TQBJAFMAUwBJAE8ATgAgACYAIABDAE8ATgBEAEkAVABJAE8ATgBTAAoAUABlAHIAbQBpAHMAcwBpAG8AbgAgAGkAcwAgAGgAZQBy
AGUAYgB5ACAAZwByAGEAbgB0AGUAZAAsACAAZgByAGUAZQAgAG8AZgAgAGMAaABhAHIAZwBlACwAIAB0AG8AIABhAG4AeQAgAHAA
ZQByAHMAbwBuACAAbwBiAHQAYQBpAG4AaQBuAGcAIABhACAAYwBvAHAAeQAgAG8AZgAgAHQAaABlACAARgBvAG4AdAAgAFMAbwBm
AHQAdwBhAHIAZQAsACAAdABvACAAdQBzAGUALAAgAHMAdAB1AGQAeQAsACAAYwBvAHAAeQAsACAAbQBlAHIAZwBlACwAIABlAG0A
YgBlAGQALAAgAG0AbwBkAGkAZgB5ACwAIAByAGUAZABpAHMAdAByAGkAYgB1AHQAZQAsACAAYQBuAGQAIABzAGUAbABsACAAbQBv
AGQAaQBmAGkAZQBkACAAYQBuAGQAIAB1AG4AbQBvAGQAaQBmAGkAZQBkACAAYwBvAHAAaQBlAHMAIABvAGYAIAB0AGgAZQAgAEYA
bwBuAHQAIABTAG8AZgB0AHcAYQByAGUALAAgAHMAdQBiAGoAZQBjAHQAIAB0AG8AIAB0AGgAZQAgAGYAbwBsAGwAbwB3AGkAbgBn
ACAAYwBvAG4AZABpAHQAaQBvAG4AcwA6AAoACgAxACkAIABOAGUAaQB0AGgAZQByACAAdABoAGUAIABGAG8AbgB0ACAAUwBvAGYA
dAB3AGEAcgBlACAAbgBvAHIAIABhAG4AeQAgAG8AZgAgAGkAdABzACAAaQBuAGQAaQB2AGkAZAB1AGEAbAAgAGMAbwBtAHAAbwBu
AGUAbgB0AHMALAAgAGkAbgAgAE8AcgBpAGcAaQBuAGEAbAAgAG8AcgAgAE0AbwBkAGkAZgBpAGUAZAAgAFYAZQByAHMAaQBvAG4A
cwAsACAAbQBhAHkAIABiAGUAIABzAG8AbABkACAAYgB5ACAAaQB0AHMAZQBsAGYALgAKAAoAMgApACAATwByAGkAZwBpAG4AYQBs
ACAAbwByACAATQBvAGQAaQBmAGkAZQBkACAAVgBlAHIAcwBpAG8AbgBzACAAbwBmACAAdABoAGUAIABGAG8AbgB0ACAAUwBvAGYA
dAB3AGEAcgBlACAAbQBhAHkAIABiAGUAIABiAHUAbgBkAGwAZQBkACwAIAByAGUAZABpAHMAdAByAGkAYgB1AHQAZQBkACAAYQBu
AGQALwBvAHIAIABzAG8AbABkACAAdwBpAHQAaAAgAGEAbgB5ACAAcwBvAGYAdAB3AGEAcgBlACwAIABwAHIAbwB2AGkAZABlAGQA
IAB0AGgAYQB0ACAAZQBhAGMAaAAgAGMAbwBwAHkAIABjAG8AbgB0AGEAaQBuAHMAIAB0AGgAZQAgAGEAYgBvAHYAZQAgAGMAbwBw
AHkAcgBpAGcAaAB0ACAAbgBvAHQAaQBjAGUAIABhAG4AZAAgAHQAaABpAHMAIABsAGkAYwBlAG4AcwBlAC4AIABUAGgAZQBzAGUA
IABjAGEAbgAgAGIAZQAgAGkAbgBjAGwAdQBkAGUAZAAgAGUAaQB0AGgAZQByACAAYQBzACAAcwB0AGEAbgBkAC0AYQBsAG8AbgBl
ACAAdABlAHgAdAAgAGYAaQBsAGUAcwAsACAAaAB1AG0AYQBuAC0AcgBlAGEAZABhAGIAbABlACAAaABlAGEAZABlAHIAcwAgAG8A
cgAgAGkAbgAgAHQAaABlACAAYQBwAHAAcgBvAHAAcgBpAGEAdABlACAAbQBhAGMAaABpAG4AZQAtAHIAZQBhAGQAYQBiAGwAZQAg
AG0AZQB0AGEAZABhAHQAYQAgAGYAaQBlAGwAZABzACAAdwBpAHQAaABpAG4AIAB0AGUAeAB0ACAAbwByACAAYgBpAG4AYQByAHkA
IABmAGkAbABlAHMAIABhAHMAIABsAG8AbgBnACAAYQBzACAAdABoAG8AcwBlACAAZgBpAGUAbABkAHMAIABjAGEAbgAgAGIAZQAg
AGUAYQBzAGkAbAB5ACAAdgBpAGUAdwBlAGQAIABiAHkAIAB0AGgAZQAgAHUAcwBlAHIALgAKAAoAMwApACAATgBvACAATQBvAGQA
aQBmAGkAZQBkACAAVgBlAHIAcwBpAG8AbgAgAG8AZgAgAHQAaABlACAARgBvAG4AdAAgAFMAbwBmAHQAdwBhAHIAZQAgAG0AYQB5
ACAAdQBzAGUAIAB0AGgAZQAgAFIAZQBzAGUAcgB2AGUAZAAgAEYAbwBuAHQAIABOAGEAbQBlACgAcwApACAAdQBuAGwAZQBzAHMA
IABlAHgAcABsAGkAYwBpAHQAIAB3AHIAaQB0AHQAZQBuACAAcABlAHIAbQBpAHMAcwBpAG8AbgAgAGkAcwAgAGcAcgBhAG4AdABl
AGQAIABiAHkAIAB0AGgAZQAgAGMAbwByAHIAZQBzAHAAbwBuAGQAaQBuAGcAIABDAG8AcAB5AHIAaQBnAGgAdAAgAEgAbwBsAGQA
ZQByAC4AIABUAGgAaQBzACAAcgBlAHMAdAByAGkAYwB0AGkAbwBuACAAbwBuAGwAeQAgAGEAcABwAGwAaQBlAHMAIAB0AG8AIAB0
AGgAZQAgAHAAcgBpAG0AYQByAHkAIABmAG8AbgB0ACAAbgBhAG0AZQAgAGEAcwAgAHAAcgBlAHMAZQBuAHQAZQBkACAAdABvACAA
dABoAGUAIAB1AHMAZQByAHMALgAKAAoANAApACAAVABoAGUAIABuAGEAbQBlACgAcwApACAAbwBmACAAdABoAGUAIABDAG8AcAB5
AHIAaQBnAGgAdAAgAEgAbwBsAGQAZQByACgAcwApACAAbwByACAAdABoAGUAIABBAHUAdABoAG8AcgAoAHMAKQAgAG8AZgAgAHQA
aABlACAARgBvAG4AdAAgAFMAbwBmAHQAdwBhAHIAZQAgAHMAaABhAGwAbAAgAG4AbwB0ACAAYgBlACAAdQBzAGUAZAAgAHQAbwAg
AHAAcgBvAG0AbwB0AGUALAAgAGUAbgBkAG8AcgBzAGUAIABvAHIAIABhAGQAdgBlAHIAdABpAHMAZQAgAGEAbgB5ACAATQBvAGQA
aQBmAGkAZQBkACAAVgBlAHIAcwBpAG8AbgAsACAAZQB4AGMAZQBwAHQAIAB0AG8AIABhAGMAawBuAG8AdwBsAGUAZABnAGUAIAB0
AGgAZQAgAGMAbwBuAHQAcgBpAGIAdQB0AGkAbwBuACgAcwApACAAbwBmACAAdABoAGUAIABDAG8AcAB5AHIAaQBnAGgAdAAgAEgA
bwBsAGQAZQByACgAcwApACAAYQBuAGQAIAB0AGgAZQAgAEEAdQB0AGgAbwByACgAcwApACAAbwByACAAdwBpAHQAaAAgAHQAaABl
AGkAcgAgAGUAeABwAGwAaQBjAGkAdAAgAHcAcgBpAHQAdABlAG4AIABwAGUAcgBtAGkAcwBzAGkAbwBuAC4ACgAKADUAKQAgAFQA
aABlACAARgBvAG4AdAAgAFMAbwBmAHQAdwBhAHIAZQAsACAAbQBvAGQAaQBmAGkAZQBkACAAbwByACAAdQBuAG0AbwBkAGkAZgBp
AGUAZAAsACAAaQBuACAAcABhAHIAdAAgAG8AcgAgAGkAbgAgAHcAaABvAGwAZQAsACAAbQB1AHMAdAAgAGIAZQAgAGQAaQBzAHQA
cgBpAGIAdQB0AGUAZAAgAGUAbgB0AGkAcgBlAGwAeQAgAHUAbgBkAGUAcgAgAHQAaABpAHMAIABsAGkAYwBlAG4AcwBlACwAIABh
AG4AZAAgAG0AdQBzAHQAIABuAG8AdAAgAGIAZQAgAGQAaQBzAHQAcgBpAGIAdQB0AGUAZAAgAHUAbgBkAGUAcgAgAGEAbgB5ACAA
bwB0AGgAZQByACAAbABpAGMAZQBuAHMAZQAuACAAVABoAGUAIAByAGUAcQB1AGkAcgBlAG0AZQBuAHQAIABmAG8AcgAgAGYAbwBu
AHQAcwAgAHQAbwAgAHIAZQBtAGEAaQBuACAAdQBuAGQAZQByACAAdABoAGkAcwAgAGwAaQBjAGUAbgBzAGUAIABkAG8AZQBzACAA
bgBvAHQAIABhAHAAcABsAHkAIAB0AG8AIABhAG4AeQAgAGQAbwBjAHUAbQBlAG4AdAAgAGMAcgBlAGEAdABlAGQAIAB1AHMAaQBu
AGcAIAB0AGgAZQAgAEYAbwBuAHQAIABTAG8AZgB0AHcAYQByAGUALgAKAAoAVABFAFIATQBJAE4AQQBUAEkATwBOAAoAVABoAGkA
cwAgAGwAaQBjAGUAbgBzAGUAIABiAGUAYwBvAG0AZQBzACAAbgB1AGwAbAAgAGEAbgBkACAAdgBvAGkAZAAgAGkAZgAgAGEAbgB5
ACAAbwBmACAAdABoAGUAIABhAGIAbwB2AGUAIABjAG8AbgBkAGkAdABpAG8AbgBzACAAYQByAGUAIABuAG8AdAAgAG0AZQB0AC4A
CgAKAEQASQBTAEMATABBAEkATQBFAFIACgBUAEgARQAgAEYATwBOAFQAIABTAE8ARgBUAFcAQQBSAEUAIABJAFMAIABQAFIATwBW
AEkARABFAEQAIAAiAEEAUwAgAEkAUwAiACwAIABXAEkAVABIAE8AVQBUACAAVwBBAFIAUgBBAE4AVABZACAATwBGACAAQQBOAFkA
IABLAEkATgBEACwAIABFAFgAUABSAEUAUwBTACAATwBSACAASQBNAFAATABJAEUARAAsACAASQBOAEMATABVAEQASQBOAEcAIABC
AFUAVAAgAE4ATwBUACAATABJAE0ASQBUAEUARAAgAFQATwAgAEEATgBZACAAVwBBAFIAUgBBAE4AVABJAEUAUwAgAE8ARgAgAE0A
RQBSAEMASABBAE4AVABBAEIASQBMAEkAVABZACwAIABGAEkAVABOAEUAUwBTACAARgBPAFIAIABBACAAUABBAFIAVABJAEMAVQBM
AEEAUgAgAFAAVQBSAFAATwBTAEUAIABBAE4ARAAgAE4ATwBOAEkATgBGAFIASQBOAEcARQBNAEUATgBUACAATwBGACAAQwBPAFAA
WQBSAEkARwBIAFQALAAgAFAAQQBUAEUATgBUACwAIABUAFIAQQBEAEUATQBBAFIASwAsACAATwBSACAATwBUAEgARQBSACAAUgBJ
AEcASABUAC4AIABJAE4AIABOAE8AIABFAFYARQBOAFQAIABTAEgAQQBMAEwAIABUAEgARQAgAEMATwBQAFkAUgBJAEcASABUACAA
SABPAEwARABFAFIAIABCAEUAIABMAEkAQQBCAEwARQAgAEYATwBSACAAQQBOAFkAIABDAEwAQQBJAE0ALAAgAEQAQQBNAEEARwBF
AFMAIABPAFIAIABPAFQASABFAFIAIABMAEkAQQBCAEkATABJAFQAWQAsACAASQBOAEMATABVAEQASQBOAEcAIABBAE4AWQAgAEcA
RQBOAEUAUgBBAEwALAAgAFMAUABFAEMASQBBAEwALAAgAEkATgBEAEkAUgBFAEMAVAAsACAASQBOAEMASQBEAEUATgBUAEEATAAs
ACAATwBSACAAQwBPAE4AUwBFAFEAVQBFAE4AVABJAEEATAAgAEQAQQBNAEEARwBFAFMALAAgAFcASABFAFQASABFAFIAIABJAE4A
IABBAE4AIABBAEMAVABJAE8ATgAgAE8ARgAgAEMATwBOAFQAUgBBAEMAVAAsACAAVABPAFIAVAAgAE8AUgAgAE8AVABIAEUAUgBX
AEkAUwBFACwAIABBAFIASQBTAEkATgBHACAARgBSAE8ATQAsACAATwBVAFQAIABPAEYAIABUAEgARQAgAFUAUwBFACAATwBSACAA
SQBOAEEAQgBJAEwASQBUAFkAIABUAE8AIABVAFMARQAgAFQASABFACAARgBPAE4AVAAgAFMATwBGAFQAVwBBAFIARQAgAE8AUgAg
AEYAUgBPAE0AIABPAFQASABFAFIAIABEAEUAQQBMAEkATgBHAFMAIABJAE4AIABUAEgARQAgAEYATwBOAFQAIABTAE8ARgBUAFcA
QQBSAEUALgBoAHQAdABwADoALwAvAHMAYwByAGkAcAB0AHMALgBzAGkAbAAuAG8AcgBnAC8ATwBGAEwAAAAAAwAAAAAAAP+1ADIA
AAAAAAAAAAAAAAAAAAAAAAAAAAABAAAADAAAAAAAAAACAA0AAgCAAAEAgQCBAAIAggCYAAEAmQCZAAIAmgCfAAEAoACgAAIAoQDr
AAEA7ADtAAIA7gEJAAEBCgELAAIBDAGaAAEBmwGeAAIBnwGkAAEAAAABAAAACgA2AFAAAkRGTFQADkxBVE4AGgAEAAAAAP//AAEA
AAAAAAFsYXRuAAoAAP//AAEAAQACa2VybgAOa2VybgAUAAAAAQAAAAAAAQAAAAEABAACAAgAAgAKCboAAQj4AAQAAABkANIBFAEU
ASIBMAFaAWABbgF4AYYBkAG2AbwBzgHOAdQB8gHyAhwCKgLEAs4DYAOiA7gDwgPUBFICxARcBQYFEAXmBqgG0gbcBuYG3Ab8BFIG
3AbcBw4EUgccByYHHAHUAdQB1AHUAdQB1ALEAhwDuAPCA8IDwgPCA8IDwgUGBQYFBgUGBqgG0gbSBtIG0gbSBtIG0gbmBtwG3Abc
BtwG3AbcBtwG3AbcBtwHHAbcBxwDogaoBvwHUAd2B4gBzgeqCEwI7gLEBFIAEAAk/9sAN//bADn/2wA6/9sAPP/bAHv/2wB8/9sA
ff/bAH7/2wB//9sAgP/bAIH/2wCX/9sBLv/bAXn/2wF8/9sAAwAD/9sBev/bAX3/2wADABT/0QAZABcAGv/hAAoAE//BABT/mgAV
/+kAFv/RABf/ugAY/9kAGf/RABr/qgAb/+kAHP+yAAEAFP/RAAMAFP/JABr/2QAc/+EAAgAU/9EAGv/ZAAMAFP/JABr/4QAc/+EA
AgAU/9kAGv/pAAkAE//KABT/wgAV/9kAFv/ZABf/mgAZ/8kAGv/xABv/4QAc/+kAAQAU/9kABAAU/8kAFf/wABr/6QAb//AAAQAD
/9sABwA3/+4AOf+1ADr/zgBZ/9sAWv/nAXr/tgF9/7YACgAP/9sAEf/bACT/7gB7/+4AfP/uAH3/7gB+/+4Af//uAID/7gCB/+4A
AwAP/9sAEf/bADn/7gAmAA//gwAR/4MAJP/OAET/vwBI/8kATP/2AFL/yQBV//YAe//OAHz/zgB9/84Afv/OAH//zgCA/84Agf/O
AJr/vwCb/78AnP+/AJ3/vwCe/78An/+/AKD/vwCi/8kAo//JAKT/yQCl/8kApv/4AKf/9gCo//gAqf/2AKz/yQCt/8kArv/JAK//
yQCw/8kAsv/JAOv/9gEL/8kAAgAP/9sAEf/bACQAD/+2ABH/tgAk/+4ARP/nAEj/5wBS/+cAWP/nAHv/7gB8/+4Aff/uAH7/7gB/
/+4AgP/uAIH/7gCa/+cAm//nAJz/5wCd/+cAnv/nAJ//5wCg/+cAov/nAKP/5wCk/+cApf/nAKz/5wCt/+cArv/nAK//5wCw/+cA
sv/nALP/5wC0/+cAtf/nALb/5wEL/+cAEABIAAoAUgAKAFz/5wCiAAoAowAKAKQACgClAAoArAAKAK0ACgCuAAoArwAKALAACgCy
AAoAt//nALn/5wELAAoABQA3/7UAOf+lADr/tgF6/5wBff+cAAIAD//JABH/yQAEAA//2wAR/9sANwAKADn/7gAfAA//gwAR/4MA
JP/JAET/2wBI/9sAUv/bAHv/yQB8/8kAff/JAH7/yQB//8kAgP/JAIH/yQCa/9sAm//bAJz/2wCd/9sAnv/bAJ//2wCg/9sAov/b
AKP/2wCk/9sApf/bAKz/2wCt/9sArv/bAK//2wCw/9sAsv/bAQv/2wACAA//5wAR/+cAKgAP/4MAEP+cABH/gwAd/9sAHv/bACT/
7gAyAAoARP/JAEj/yQBS/8kAe//uAHz/7gB9/+4Afv/uAH//7gCA/+4Agf/uAI0ACgCOAAoAjwAKAJAACgCRAAoAkgAKAJr/8gCb
/8kAnP/yAJ3/8gCe/8kAn//kAKD/yQCi/+QAo//JAKT/5ACl/+QArP/XAK3/yQCu/9cAr//JALD/5ACy/8kBCgAKAQv/yQACAA//
nAAR/5wANQAP/4MAEP+cABH/gwAd/7UAHv+1ACT/tgAy/+4ARP+rAEj/tQBM/+4AUv+1AFj/tQB7/7YAfP+2AH3/tgB+/7YAf/+2
AID/tgCB/7YAjf/uAI7/7gCP/+4AkP/uAJH/7gCS/+4Amv/AAJv/qwCc/8AAnf/AAJ7/1QCf/8AAoP+rAKL/yACj/7UApP+1AKX/
2gCm/+4Ap//uAKj/9wCp/+4ArP+1AK3/tQCu/7UAr/+1ALD/yACy/7UAs/+1ALT/tQC1/7UAtv+1AOv/7gEK/+4BC/+1ADAAD/+D
ABD/nAAR/4MAHf+cAB7/nAAk/84ARP+1AEj/xABM/+4AUv/EAFj/yQBc/8kAe//OAHz/zgB9/84Afv/OAH//zgCA/84Agf/OAJr/
tQCb/7UAnP+1AJ3/tQCe/8gAn/+1AKD/tQCi/8QAo//EAKT/xACl/8QApv/uAKf/7gCo/+4Aqf/uAKz/xACt/8QArv/EAK//xACw
/9MAsv/EALP/yQC0/8kAtf/JALb/1wC3/8kAuf/JAOv/7gEL/8QACgAP/5wAEP+DABH/nAAd/7UAHv+1AJr/xACi/8QApf/EAKz/
xACw/8QAAgBZ//YAWv/2AAIAD//uABH/7gAFAA//7gAR/+4AS//5AE7/+QBP//kABAAP/9sAEf/bAXoAZAF9AGQAAwAP/5wAEP/b
ABH/nAACAA//gwAR/4MACgAP/4MAEf+DAET/7gCa/+4Am//uAJz/7gCd/+4Anv/uAJ//7gCg/+4ACQAk/7YAe/+2AHz/tgB9/7YA
fv+2AH//tgCA/7YAgf+2AXn/5wAEAEf/2wBW/+cBev/nAaL/5wAIACT/tgB7/7YAfP+2AH3/tgB+/7YAf/+2AID/tgCB/7YAKABE
/+IARf/iAEb/2ABH/9gASP/OAEr/7ABS/8QAU//OAFT/zgBW/+wAV//IAFj/zgBZ/84AWv/OAFz/zgBd/+wAmv/iAJv/4gCc/+IA
nf/iAJ7/4gCf/+IAoP/iAKL/zgCj/84ApP/OAKX/zgCs/8QArf/EAK7/xACv/8QAsP/EALL/xACz/84AtP/OALX/zgC2/84At//O
ALn/zgEL/8QAKABE/9gARf/YAEb/zgBH/84ASP/OAE3/9gBS/84AU//EAFT/xABW/+wAV//EAFj/xABZ/84AWv/OAFz/zgBd/+wA
mv/YAJv/2ACc/9gAnf/YAJ7/2ACf/9gAoP/YAKL/zgCj/84ApP/OAKX/zgCs/84Arf/OAK7/zgCv/84AsP/OALL/zgCz/8QAtP/E
ALX/xAC2/8QAt//OALn/zgEL/84AAgF6/5wBff+cAAIAHgADAAMAAAAPAA8AAQARABEAAgATAB4AAwAkACcADwApACoAEwAtAC8A
FQAxADQAGAA2ADoAHAA8ADwAIQBEAEYAIgBIAEoAJQBSAFMAKABVAFYAKgBZAFoALABcAFwALgB7AIAALwCCAIIANQCLAJcANgCa
AKUAQwCsALAATwCyALIAVAC3ALkAVQD6APoAWAEuAS4AWQE1ATUAWgF5AXoAWwF8AX0AXQGdAZ8AXwGhAaIAYgACAMAABAAAAQgB
ZgAIAAsAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD/4gAAAAAAAAAAAAAAAAAAAAAAAAAA/7X/nP/u/5z/7v+c/6UAAAAAAAAAAAAA
AAAAAAAAAAAAAAAA//YAAAAAAAAAAAAAAAAAAAAAAAAAAP/b/+L/tQAAAAAAAAAAAAAAAAAAAAAAAAAA/+4AAAAAAAAAAAAAAAAA
AAAA/+cAAP+2AAAAAAAAAAAAAAAAAAAAAAAAAAD/7gABACIAJAAnAC8AMgA4ADwARAB7AHwAfQB+AH8AgACLAI0AjgCPAJAAkQCS
AJMAlACVAJYAlwCaAJsAnACdAJ4AnwCgAPoBLgACAA8AJAAkAAQAJwAnAAUALwAvAAYAMgAyAAcAOAA4AAEAPAA8AAIARABEAAMA
ewCAAAQAiwCLAAUAjQCSAAcAkwCWAAEAlwCXAAIAmgCgAAMA+gD6AAYBLgEuAAIAAgAaACQAJAABADIAMgADADgAOAAJADwAPAAK
AEQARAACAEgASAAEAEwATAAFAFIAUgAGAFgAWAAHAFwAXAAIAHsAgQABAI0AkgADAJMAlgAJAJcAlwAKAJoAoAACAKIApQAEAKYA
qQAFAKwAsAAGALIAsgAGALMAtgAHALcAtwAIALkAuQAIAOsA6wAFAQoBCgADAQsBCwAGAS4BLgAKAAEAAAAKAEgAbgADREZMVAAU
TEFUTgAgbGF0bgAyAAQAAAAA//8AAQAAAAAAAWxhdG4ACgAA//8AAQABAAQAAAAA//8AAQACAANsaWdhABRsaWdhABpsaWdhACAA
AAABAAAAAAABAAAAAAABAAEAAgAGAA4ABAAAAAEAEAAEAAAAAQAoAAEAGgABAAgAAgAGAAwBnQACAEwBngACAE8AAQABAEkAAQAa
AAEACAACAAYADAGdAAIATAGeAAIATwABAAEASQAAAAEAAAAB
""".replace("\n", ""))
ACADEMICO_BOLD = _b64.b64decode("""
T1RUTwANAIAAAwBQQ0ZGIHn8s5YAAA1QAACMRkRTSUcAAAACAADsVAAAAAhHREVGCsIMWQAA4oAAAABeR1BPU7RKru8AAOLgAAAI
sEdTVUK5ir9OAADrkAAAAMRPUy8ycE+FxQAAAUAAAABgY21hcAy6zEAAAAhUAAAE/GhlYWQqn2yOAAAA3AAAADZoaGVhB7AEWgAA
ARQAAAAkaG10eO/1JYoAAAGgAAAGtG1heHABrVAAAAABOAAAAAZuYW1lQ+7MkAAAmZgAAEjIcG9zdP+4ADIAAOJgAAAAIAABAAAA
AOeuHig1A18PPPUAAwPoAAAAAOPXnwYAAAAA49eh/f9b/lIEfQSrAAEAAwACAAAAAAAAAAEAAAPU/wYAAASH/1v/HwR+AAEAAAAA
AAAAAAAAAAAAAAGtAABQAAGtAAAABAJaArwABQAAAooCWAAAAEsCigJYAAABXgAyARYAAAIEBgMFBwUCAwQAAAAHAAAAAAAAAAAA
AAAAU01URwAgAAD7AgLu/wYA5gPUAPogAAABAAAAAAHQAtIAAAAgAAIBFgAAAAAAAAEfAAABHwAAAQcALwFNAAACYwAhAiUAGQMS
AAwDPgAlAMwAHgGiAE0BmgApAhQANgJeADIBFgAoAYgAIgEWACwBFv/WAj4AGwIlAEUCBgAcAfsAHAICAA4B+AAcAhgAGwIAABcC
DQAbAhQAGwEWACwBFgAoAnYAMgJeADICdAAyAaAAFwLr//4C3v/tAwoAEwLNACMDQQATAuEAEwK4ABMDKQAnAysAEwGnABkCRwAG
AxAAEwK0ABMDsAAKAxoABQMeACcCzQAcAysAJwLpAB4CmwAzArQAEAMnAA4C6f/tBCUABwLt//QCw//0AocAHAE5ADICXgB6AU0A
PAH6AB0B9AAAATgAAAJWABkCXgAEAg8AFgJ4ABICFgAWAY0AEgJAABcCoQAZAVQAGgEw/7gChQAZAU0AEgPuABkCoQAZAjkAFgJ+
ABYCeAAgAeUAGQHRABgBvAAOAo8AFgJpABIDSwAKAlQADAJgAA4B9AAZAVsALwJvARIBWgA8Al4ASAEoAEkCJQAWAkMADwJg//QB
rQAxAU3/9ANB//YBbwAAAckAGQJeADIC6//+AS3/+gGQADkCXgAyAU0AVAKLAAwCyQBfARYAQwFNABEBUQAAAc8AKwOPAC4DogAu
A4IACAGrABsC2P/jAtb/4wLa/+0C0v/jAuX/7gLh/+0EFv/jAwoALgLjABMC4wATAvcAEwLhABMBrQAdAbEAHQGvAB0BtAAdA0EA
EwMeAAUDKwAnAysAJwMpACcDKQAnA0EAJwMpACcDJwAOAykADgMnAA4DKQAOAsP/9ALYABMCY//+AmMAKAJjACgCYwAoAmMAKAJj
ACgCYwAoAzwAIAIJABYCDwAWAgkAFgIPABYCDwAWATsACgE/ABIBYgALAWn//wJfAB8CoQAZAjkAFgI5ABYCQAAWAjkAFgI5ABYC
XgAyAkMAFgKhABYCmgAWApoAFgKhABYCYAAOApQAEgJgAA4C3v/tAlYAGQLe/+0CVgAZAt7/7QJWABkCzQAjAg8AFgLNACMCDwAW
As0AIwIPABYCzQAjAg8AFgNBABMCdAASA0EAEwJ4ABIC4QATAhYAFgLhABMCFgAWAuEAEwIWABYC4QATAhYAFgLhABMCFgAWAykA
JwJAABcDKQAnAkAAFwMpACcCQAAXAykAJwJAABcDKwATAqEAGQMrABMCoQAZAacAGAE7/+IBpwAZATsAAQGnABkBOwAAAacAGQFU
ABoBpwAZATsAEgPuABkChAAaAkcABgEw/7gDEAATAoUAGQK0ABMBTQASArQAEwFNABICtAATAU8AEgK0ABMBhwASArQAEwFNABID
GgAFAqEAGQMaAAUCoQAZAxoABQKhABkDGgAFAqEAGQMeACcCOQAWAx4AJwI5ABYDHgAnAjkAFgP2AAADiwAgAukAHgHlABkC6QAe
AeUAGQLpAB4B5QAZApsAMwHRABgCmwAzAdEAGAKbADMB0QAYApsAMwHRABgCtAAQAbwADgK0ABABqwAOAycADgKPABYDJwAOAo8A
FgMnAA4CjwAWAycADgKPABYDJwAOAo8AFgMnAA4CjwAWBCUABwNLAAoCw//0AmAADgK8//QChwAcAfQAGQKHABwB9AAZAocAHAH0
ABkBjQASAuEAEwJ8AA4DHgAnAjkAFgMnAA4CsgAWAt7/7QJWABkBpwAZATsAAAMeACcCOQAWAycADgKPABYDJwAOAo8AFgMnAA4C
jwAWAycADgKhABYCFgAWAykAJwJAABcDHgAnAjkAFgEw/7gDKQAnAkAAFwLe/+0CVgAZBBb/4wM8ACADHgAnAjkAFgLe/+0CVgAZ
AuEAEwIWABYBpwAZAVT/zQMeACcCOQAWAukAHgHlABkDJwAOAo8AFgKbADMB0QAYArQAEAG8AA4BMP+4AhYAFgIWABYBpgAvAZwA
LwEn//YBJP/2AU0ACQFNAF8BTQA6AU0AqAFN/+gBTf/wAxYAIQJLABEC6QAeAhgAHQIsAAAD6AAAAOQAGQDiABkAzAAMAcAAFgHA
ABYBtAAQAh0AKAH0ACgCXgB6A5AAQgSHAAMBKQAdAgIAHQEDABkBAwAmAKf/WwJJAAUDpwAGA4oALgJAADoCcgAjArIAFwI0ABoC
XAAlAvIALAHLAAcCHQAeAmUAMgKDADYCawAxAjwAJwGrACgBLAAoAZAAKAKAAAEClAASAmMAAQJjABIDQQATAr7/9ALYABMCPAAW
AmoADgJtABICvAATATsAEgKbADMB5wAwAnwAHAH4ABkAAAADAAAAAwAAAiYAAQAAAAAAHAADAAEAAAImAAYCCgAAAAABAAABAAAA
AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAwAEAAUABgAHAAgACQAK
AAsADAANAA4ADwAQABEAEgATABQAFQAWABcAGAAZABoAGwAcAB0AHgAfACAAIQAiACMAJAAlACYAJwAoACkAKgArACwALQAuAC8A
MAAxADIAMwA0ADUANgA3ADgAOQA6ADsAPAA9AD4APwBAAEEAQgBDAEQARQBGAEcASABJAEoASwBMAE0ATgBPAFAAUQBSAFMAVABV
AFYAVwBYAFkAWgBbAFwAXQBeAF8AYABhAAAAfwCAAIIAhACMAJEAlgCbAJoAnACeAJ0AnwChAKMAogCkAKUApwCmAKgAqQCrAK0A
rACuALAArwC0ALMAtQC2AYEAbgBjAGQAZgGDAHIAmQBsAGgBjABwAGcBlgCBAJIBkwBvAZcBmABlAHEBjgGRAZABdgGUAGkAdQAA
AKAAsgB6AGIAawGSATcBlQGPAGoAdgGEAAAAewB+AJABCgELAXkBegF+AX8BewF8ALEBmQC5AS4BigGLAYgBiQGdAZ4BggBzAX0B
gAGFAH0AhQB8AIYAgwCIAIkAigCHAI4AjwAAAI0AlACVAJMA6wFtAXMAbQFvAXABcQB0AXQBcgFuAAQC1gAAAIAAgAAGAAAAAAB+
AKMApQCsALEAuADWATcBSAFlAX8BjgGSAaEBsAHUAd0B5wHrAfAB9QIBAgUCCQINAhECFQIbAjcCWQK/AscC3QOpA8AELwRPIBQg
GiAeICIgJiAwIDMgOiBEIKwhIiFbIgIiBiIPIhEiGiIeIisiSCJgImUlyiZv+wL//wAAAAAAIAChAKUApwCuALQAugDYATkBSgFo
AY4BkgGgAa8BzQHXAeYB6gHwAfQB+gIEAggCDAIQAhQCGAI3AlgCvgLGAtgDqQPABC8ETyATIBggHCAgICYgMCAyIDkgRCCsISIh
WyICIgYiDyIRIhoiHiIrIkgiYCJkJcombfsB//8AAf/jAAD/wAAAAAAAAP+7/7r/uf+4/7b/qP+lAAAAAAAAAAAAAAAA/18AAAAA
AAAAAAAAAAAAAAAA/zEAAAAAAAAAAP3M/bb9SP0pAAAAAAAAAADhXuFVAAAAAOFG4N/gauAy34zfid+B34DfeN9132nfTd82AADb
zwAAAAAAAQAAAAAAfAAAAH4AiACOAAAAAAAAAAAAAAAAAAAAiACKAIwAmgCmAKgAAACoAKoAuAC6ALwAvgDAAMIAAADGAMgAygDM
AAAAAAAAAAAAzgDQANQA2AAAAAAA2ADaAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAwgAAAMIAxgAAAGIAYwBkAGYAZwBoAGkA
agBrAGwAbQBuAG8AcABxAHIAcwB0ATgBOQE6ATsBPAE9AT4BPwFAAUEBQgFDAUQBRQFGAUcBSAFJAUoBSwFMAU0BTgFQAVEBUgFT
AVQBVQFWAVcBWAFZAVoBWwFcAV0BXgFfAWABYQFiAWMBZAFlAWYBZwFpAWoBawFsAW0BbgFvAXABcQFyAXMBdAF5AXoBewF8AX0B
fgF/AYABgQGCAYMBhgGHAYgBiQGXAZgBmgGbAZwBnQGeAQAEAgABAQEPQWNhZGVtaWNvLUJvbGQAAQEBLfjqAPjrDAD47AL47QP4
FAQc/1sc/lIcBH4cBKsFHC4kDxwvkxGwHQAAgEYSANMCAAEACAAKABEAGAAfACUAKwAyADkAPwBFAFAAWwBlAG8AdQB7AIEAhwCN
AJMAmgChAKcArQC3AMEAyADPANUA2wDmAPEA9wD9AQcBEQEYAR8BKgE1ATkBPQFDAUkBUAFXAV0BYwFqAXEBewF9AX8BigGVAZwB
owGpAa8BtgG9AcMByQHNAdEB1wHdAeQB6wHxAfcB+gH9AgQCCwIRAhcCJAIxAjcCPQJEAksCUQJXAl0CYwJuAnkCgQKJApAClwKd
AqMCqQKvArYCvQLDAskCzgLTAuAC7QL0AvsDBgMRAxwDJwMtAzMDPQNHA0wDUwNYA10DYgNnA24DdQN8A4MDigORA5gDnwOmA60D
tAO7A8IDyQPQA9YD3APjA+oD8QP4A/8ECQQTBBoEIQQsBDcEPgRFBEwEUwRaBGEEaARvBHYEfQSEBIsEkgSZBKAEpwSuBLUEvATD
BMoE0QTTBNoE4QTnBO0E8QT8BQMFCgUTBRoFIgUqBTUFPQVGBVIFWQVgBWcFbgVxBXQFewWFBY4FlQWfBagFsgW8BcYF0AXaBeQF
8RdUF2IXa3VuaTAwMDBDUnVuaTAwQjVBbWFjcm9uYW1hY3JvbkFicmV2ZWFicmV2ZUFvZ29uZWthb2dvbmVrQ2FjdXRlY2FjdXRl
Q2NpcmN1bWZsZXhjY2lyY3VtZmxleENkb3RhY2NlbnRjZG90YWNjZW50Q2Nhcm9uY2Nhcm9uRGNhcm9uZGNhcm9uRGNyb2F0ZGNy
b2F0RW1hY3JvbmVtYWNyb25FYnJldmVlYnJldmVFZG90YWNjZW50ZWRvdGFjY2VudEVvZ29uZWtlb2dvbmVrRWNhcm9uZWNhcm9u
R2NpcmN1bWZsZXhnY2lyY3VtZmxleEdicmV2ZWdicmV2ZUdkb3RhY2NlbnRnZG90YWNjZW50dW5pMDEyMnVuaTAxMjNIY2lyY3Vt
ZmxleGhjaXJjdW1mbGV4SGJhcmhiYXJJdGlsZGVpdGlsZGVJbWFjcm9uaW1hY3JvbklicmV2ZWlicmV2ZUlvZ29uZWtpb2dvbmVr
SWRvdGFjY2VudElKaWpKY2lyY3VtZmxleGpjaXJjdW1mbGV4dW5pMDEzNnVuaTAxMzdMYWN1dGVsYWN1dGV1bmkwMTNCdW5pMDEz
Q0xjYXJvbmxjYXJvbkxkb3RsZG90TmFjdXRlbmFjdXRldW5pMDE0NXVuaTAxNDZOY2Fyb25uY2Fyb25FbmdlbmdPbWFjcm9ub21h
Y3Jvbk9icmV2ZW9icmV2ZU9odW5nYXJ1bWxhdXRvaHVuZ2FydW1sYXV0UmFjdXRlcmFjdXRldW5pMDE1NnVuaTAxNTdSY2Fyb25y
Y2Fyb25TYWN1dGVzYWN1dGVTY2lyY3VtZmxleHNjaXJjdW1mbGV4U2NlZGlsbGFzY2VkaWxsYXVuaTAxNjJ1bmkwMTYzVGNhcm9u
dGNhcm9uVXRpbGRldXRpbGRlVW1hY3JvbnVtYWNyb25VYnJldmV1YnJldmVVcmluZ3VyaW5nVWh1bmdhcnVtbGF1dHVodW5nYXJ1
bWxhdXRVb2dvbmVrdW9nb25la1djaXJjdW1mbGV4d2NpcmN1bWZsZXhZY2lyY3VtZmxleHljaXJjdW1mbGV4WmFjdXRlemFjdXRl
WmRvdGFjY2VudHpkb3RhY2NlbnRsb25nc3VuaTAxOEVPaG9ybm9ob3JuVWhvcm51aG9ybnVuaTAxQ0R1bmkwMUNFdW5pMDFDRnVu
aTAxRDB1bmkwMUQxdW5pMDFEMnVuaTAxRDN1bmkwMUQ0dW5pMDFEN3VuaTAxRDh1bmkwMUQ5dW5pMDFEQXVuaTAxREJ1bmkwMURD
dW5pMDFEREdjYXJvbmdjYXJvbnVuaTAxRUF1bmkwMUVCdW5pMDFGMHVuaTAxRjR1bmkwMUY1QXJpbmdhY3V0ZWFyaW5nYWN1dGVB
RWFjdXRlYWVhY3V0ZU9zbGFzaGFjdXRlb3NsYXNoYWN1dGV1bmkwMjAwdW5pMDIwMXVuaTAyMDR1bmkwMjA1dW5pMDIwOHVuaTAy
MDl1bmkwMjBDdW5pMDIwRHVuaTAyMTB1bmkwMjExdW5pMDIxNHVuaTAyMTV1bmkwMjE4dW5pMDIxOXVuaTAyMUF1bmkwMjFCdW5p
MDIzN3VuaTAyNTh1bmkwMjU5dW5pMDJCRXVuaTAyQkZ1bmkwM0E5cGl1bmkwNDJGdW5pMDQ0Rm1pbnV0ZXNlY29uZEV1cm9wYXJ0
aWFsZGlmZnVuaTIyMDZwcm9kdWN0c3VtbWF0aW9ucmFkaWNhbGluZmluaXR5aW50ZWdyYWxhcHByb3hlcXVhbG5vdGVxdWFsbGVz
c2VxdWFsZ3JlYXRlcmVxdWFsbG96ZW5nZXVuaTI2NkR1bmkyNjZFdW5pMjY2RmZfaWZfbEV0aC4wMDFZYWN1dGUuMDAxVGhvcm4u
MDAxZXRoLjAwMXlhY3V0ZS4wMDF0aG9ybi4wMDFMc2xhc2guMDAxbHNsYXNoLjAwMVNjYXJvbi4wMDFzY2Fyb24uMDAxWmNhcm9u
LjAwMXpjYXJvbi4wMDFWZXJzaW9uIDAuOTA1Q29weXJpZ2h0IFwoY1wpIDIwMjUsIFN0ZWluYmVyZyBNZWRpYSBUZWNobm9sb2dp
ZXMgR21iSCBcKGh0dHA6Ly93d3cuc3RlaW5iZXJnLm5ldC9cKSwgd2l0aCBSZXNlcnZlZCBGb250IE5hbWUgIkFjYWRlbWljbyIu
CgpUaGlzIEZvbnQgU29mdHdhcmUgaXMgbGljZW5zZWQgdW5kZXIgdGhlIFNJTCBPcGVuIEZvbnQgTGljZW5zZSwgVmVyc2lvbiAx
LjEuIFRoaXMgbGljZW5zZSBpcyBjb3BpZWQgYmVsb3csIGFuZCBpcyBhbHNvIGF2YWlsYWJsZSB3aXRoIGEgRkFRIGF0OiBodHRw
Oi8vc2NyaXB0cy5zaWwub3JnL09GTAoKLS0tLS0tLS0tLS0tLS0tLS0tLS0tLS0tLS0tLS0tLS0tLS0tLS0tLS0tLS0tLS0tLS0t
LS0tLS0tLS0KU0lMIE9QRU4gRk9OVCBMSUNFTlNFIFZlcnNpb24gMS4xIC0gMjYgRmVicnVhcnkgMjAwNwotLS0tLS0tLS0tLS0t
LS0tLS0tLS0tLS0tLS0tLS0tLS0tLS0tLS0tLS0tLS0tLS0tLS0tLS0tLS0tLQoKUFJFQU1CTEUKVGhlIGdvYWxzIG9mIHRoZSBP
cGVuIEZvbnQgTGljZW5zZSBcKE9GTFwpIGFyZSB0byBzdGltdWxhdGUgd29ybGR3aWRlIGRldmVsb3BtZW50IG9mIGNvbGxhYm9y
YXRpdmUgZm9udCBwcm9qZWN0cywgdG8gc3VwcG9ydCB0aGUgZm9udCBjcmVhdGlvbiBlZmZvcnRzIG9mIGFjYWRlbWljIGFuZCBs
aW5ndWlzdGljIGNvbW11bml0aWVzLCBhbmQgdG8gcHJvdmlkZSBhIGZyZWUgYW5kIG9wZW4gZnJhbWV3b3JrIGluIHdoaWNoIGZv
bnRzIG1heSBiZSBzaGFyZWQgYW5kIGltcHJvdmVkIGluIHBhcnRuZXJzaGlwIHdpdGggb3RoZXJzLgoKVGhlIE9GTCBhbGxvd3Mg
dGhlIGxpY2Vuc2VkIGZvbnRzIHRvIGJlIHVzZWQsIHN0dWRpZWQsIG1vZGlmaWVkIGFuZCByZWRpc3RyaWJ1dGVkIGZyZWVseSBh
cyBsb25nIGFzIHRoZXkgYXJlIG5vdCBzb2xkIGJ5IHRoZW1zZWx2ZXMuIFRoZSBmb250cywgaW5jbHVkaW5nIGFueSBkZXJpdmF0
aXZlIHdvcmtzLCBjYW4gYmUgYnVuZGxlZCwgZW1iZWRkZWQsIHJlZGlzdHJpYnV0ZWQgYW5kL29yIHNvbGQgd2l0aCBhbnkgc29m
dHdhcmUgcHJvdmlkZWQgdGhhdCBhbnkgcmVzZXJ2ZWQgbmFtZXMgYXJlIG5vdCB1c2VkIGJ5IGRlcml2YXRpdmUgd29ya3MuIFRo
ZSBmb250cyBhbmQgZGVyaXZhdGl2ZXMsIGhvd2V2ZXIsIGNhbm5vdCBiZSByZWxlYXNlZCB1bmRlciBhbnkgb3RoZXIgdHlwZSBv
ZiBsaWNlbnNlLiBUaGUgcmVxdWlyZW1lbnQgZm9yIGZvbnRzIHRvIHJlbWFpbiB1bmRlciB0aGlzIGxpY2Vuc2UgZG9lcyBub3Qg
YXBwbHkgdG8gYW55IGRvY3VtZW50IGNyZWF0ZWQgdXNpbmcgdGhlIGZvbnRzIG9yIHRoZWlyIGRlcml2YXRpdmVzLgoKREVGSU5J
VElPTlMKIkZvbnQgU29mdHdhcmUiIHJlZmVycyB0byB0aGUgc2V0IG9mIGZpbGVzIHJlbGVhc2VkIGJ5IHRoZSBDb3B5cmlnaHQg
SG9sZGVyXChzXCkgdW5kZXIgdGhpcyBsaWNlbnNlIGFuZCBjbGVhcmx5IG1hcmtlZCBhcyBzdWNoLiBUaGlzIG1heQppbmNsdWRl
IHNvdXJjZSBmaWxlcywgYnVpbGQgc2NyaXB0cyBhbmQgZG9jdW1lbnRhdGlvbi4KCiJSZXNlcnZlZCBGb250IE5hbWUiIHJlZmVy
cyB0byBhbnkgbmFtZXMgc3BlY2lmaWVkIGFzIHN1Y2ggYWZ0ZXIgdGhlIGNvcHlyaWdodCBzdGF0ZW1lbnRcKHNcKS4KCiJPcmln
aW5hbCBWZXJzaW9uIiByZWZlcnMgdG8gdGhlIGNvbGxlY3Rpb24gb2YgRm9udCBTb2Z0d2FyZSBjb21wb25lbnRzIGFzIGRpc3Ry
aWJ1dGVkIGJ5IHRoZSBDb3B5cmlnaHQgSG9sZGVyXChzXCkuCgoiTW9kaWZpZWQgVmVyc2lvbiIgcmVmZXJzIHRvIGFueSBkZXJp
dmF0aXZlIG1hZGUgYnkgYWRkaW5nIHRvLCBkZWxldGluZywgb3Igc3Vic3RpdHV0aW5nIC0tIGluIHBhcnQgb3IgaW4gd2hvbGUg
LS0gYW55IG9mIHRoZSBjb21wb25lbnRzIG9mIHRoZSBPcmlnaW5hbCBWZXJzaW9uLCBieSBjaGFuZ2luZyBmb3JtYXRzIG9yIGJ5
IHBvcnRpbmcgdGhlIEZvbnQgU29mdHdhcmUgdG8gYSBuZXcgZW52aXJvbm1lbnQuCgoiQXV0aG9yIiByZWZlcnMgdG8gYW55IGRl
c2lnbmVyLCBlbmdpbmVlciwgcHJvZ3JhbW1lciwgdGVjaG5pY2FsIHdyaXRlciBvciBvdGhlciBwZXJzb24gd2hvIGNvbnRyaWJ1
dGVkIHRvIHRoZSBGb250IFNvZnR3YXJlLgoKUEVSTUlTU0lPTiAmIENPTkRJVElPTlMKUGVybWlzc2lvbiBpcyBoZXJlYnkgZ3Jh
bnRlZCwgZnJlZSBvZiBjaGFyZ2UsIHRvIGFueSBwZXJzb24gb2J0YWluaW5nIGEgY29weSBvZiB0aGUgRm9udCBTb2Z0d2FyZSwg
dG8gdXNlLCBzdHVkeSwgY29weSwgbWVyZ2UsIGVtYmVkLCBtb2RpZnksIHJlZGlzdHJpYnV0ZSwgYW5kIHNlbGwgbW9kaWZpZWQg
YW5kIHVubW9kaWZpZWQgY29waWVzIG9mIHRoZSBGb250IFNvZnR3YXJlLCBzdWJqZWN0IHRvIHRoZSBmb2xsb3dpbmcgY29uZGl0
aW9uczoKCjFcKSBOZWl0aGVyIHRoZSBGb250IFNvZnR3YXJlIG5vciBhbnkgb2YgaXRzIGluZGl2aWR1YWwgY29tcG9uZW50cywg
aW4gT3JpZ2luYWwgb3IgTW9kaWZpZWQgVmVyc2lvbnMsIG1heSBiZSBzb2xkIGJ5IGl0c2VsZi4KCjJcKSBPcmlnaW5hbCBvciBN
b2RpZmllZCBWZXJzaW9ucyBvZiB0aGUgRm9udCBTb2Z0d2FyZSBtYXkgYmUgYnVuZGxlZCwgcmVkaXN0cmlidXRlZCBhbmQvb3Ig
c29sZCB3aXRoIGFueSBzb2Z0d2FyZSwgcHJvdmlkZWQgdGhhdCBlYWNoIGNvcHkgY29udGFpbnMgdGhlIGFib3ZlIGNvcHlyaWdo
dCBub3RpY2UgYW5kIHRoaXMgbGljZW5zZS4gVGhlc2UgY2FuIGJlIGluY2x1ZGVkIGVpdGhlciBhcyBzdGFuZC1hbG9uZSB0ZXh0
IGZpbGVzLCBodW1hbi1yZWFkYWJsZSBoZWFkZXJzIG9yIGluIHRoZSBhcHByb3ByaWF0ZSBtYWNoaW5lLXJlYWRhYmxlIG1ldGFk
YXRhIGZpZWxkcyB3aXRoaW4gdGV4dCBvciBiaW5hcnkgZmlsZXMgYXMgbG9uZyBhcyB0aG9zZSBmaWVsZHMgY2FuIGJlIGVhc2ls
eSB2aWV3ZWQgYnkgdGhlIHVzZXIuCgozXCkgTm8gTW9kaWZpZWQgVmVyc2lvbiBvZiB0aGUgRm9udCBTb2Z0d2FyZSBtYXkgdXNl
IHRoZSBSZXNlcnZlZCBGb250IE5hbWVcKHNcKSB1bmxlc3MgZXhwbGljaXQgd3JpdHRlbiBwZXJtaXNzaW9uIGlzIGdyYW50ZWQg
YnkgdGhlIGNvcnJlc3BvbmRpbmcgQ29weXJpZ2h0IEhvbGRlci4gVGhpcyByZXN0cmljdGlvbiBvbmx5IGFwcGxpZXMgdG8gdGhl
IHByaW1hcnkgZm9udCBuYW1lIGFzIHByZXNlbnRlZCB0byB0aGUgdXNlcnMuCgo0XCkgVGhlIG5hbWVcKHNcKSBvZiB0aGUgQ29w
eXJpZ2h0IEhvbGRlclwoc1wpIG9yIHRoZSBBdXRob3JcKHNcKSBvZiB0aGUgRm9udCBTb2Z0d2FyZSBzaGFsbCBub3QgYmUgdXNl
ZCB0byBwcm9tb3RlLCBlbmRvcnNlIG9yIGFkdmVydGlzZSBhbnkgTW9kaWZpZWQgVmVyc2lvbiwgZXhjZXB0IHRvIGFja25vd2xl
ZGdlIHRoZSBjb250cmlidXRpb25cKHNcKSBvZiB0aGUgQ29weXJpZ2h0IEhvbGRlclwoc1wpIGFuZCB0aGUgQXV0aG9yXChzXCkg
b3Igd2l0aCB0aGVpciBleHBsaWNpdCB3cml0dGVuIHBlcm1pc3Npb24uCgo1XCkgVGhlIEZvbnQgU29mdHdhcmUsIG1vZGlmaWVk
IG9yIHVubW9kaWZpZWQsIGluIHBhcnQgb3IgaW4gd2hvbGUsIG11c3QgYmUgZGlzdHJpYnV0ZWQgZW50aXJlbHkgdW5kZXIgdGhp
cyBsaWNlbnNlLCBhbmQgbXVzdCBub3QgYmUgZGlzdHJpYnV0ZWQgdW5kZXIgYW55IG90aGVyIGxpY2Vuc2UuIFRoZSByZXF1aXJl
bWVudCBmb3IgZm9udHMgdG8gcmVtYWluIHVuZGVyIHRoaXMgbGljZW5zZSBkb2VzIG5vdCBhcHBseSB0byBhbnkgZG9jdW1lbnQg
Y3JlYXRlZCB1c2luZyB0aGUgRm9udCBTb2Z0d2FyZS4KClRFUk1JTkFUSU9OClRoaXMgbGljZW5zZSBiZWNvbWVzIG51bGwgYW5k
IHZvaWQgaWYgYW55IG9mIHRoZSBhYm92ZSBjb25kaXRpb25zIGFyZSBub3QgbWV0LgoKRElTQ0xBSU1FUgpUSEUgRk9OVCBTT0ZU
V0FSRSBJUyBQUk9WSURFRCAiQVMgSVMiLCBXSVRIT1VUIFdBUlJBTlRZIE9GIEFOWSBLSU5ELCBFWFBSRVNTIE9SIElNUExJRUQs
IElOQ0xVRElORyBCVVQgTk9UIExJTUlURUQgVE8gQU5ZIFdBUlJBTlRJRVMgT0YgTUVSQ0hBTlRBQklMSVRZLCBGSVRORVNTIEZP
UiBBIFBBUlRJQ1VMQVIgUFVSUE9TRSBBTkQgTk9OSU5GUklOR0VNRU5UIE9GIENPUFlSSUdIVCwgUEFURU5ULCBUUkFERU1BUkss
IE9SIE9USEVSIFJJR0hULiBJTiBOTyBFVkVOVCBTSEFMTCBUSEUgQ09QWVJJR0hUIEhPTERFUiBCRSBMSUFCTEUgRk9SIEFOWSBD
TEFJTSwgREFNQUdFUyBPUiBPVEhFUiBMSUFCSUxJVFksIElOQ0xVRElORyBBTlkgR0VORVJBTCwgU1BFQ0lBTCwgSU5ESVJFQ1Qs
IElOQ0lERU5UQUwsIE9SIENPTlNFUVVFTlRJQUwgREFNQUdFUywgV0hFVEhFUiBJTiBBTiBBQ1RJT04gT0YgQ09OVFJBQ1QsIFRP
UlQgT1IgT1RIRVJXSVNFLCBBUklTSU5HIEZST00sIE9VVCBPRiBUSEUgVVNFIE9SIElOQUJJTElUWSBUTyBVU0UgVEhFIEZPTlQg
U09GVFdBUkUgT1IgRlJPTSBPVEhFUiBERUFMSU5HUyBJTiBUSEUgRk9OVCBTT0ZUV0FSRS5BY2FkZW1pY28gQm9sZEFjYWRlbWlj
bwDGAgABAAQACAAMABMAFwBUAFcAgQCUAJwAsQC5ANwA+QEAAQQBFwEqATUBPgFFAUoBUQFVAVsBlAHGAfkB/AIgAjgCTAJQAlUC
XAJiAmgCbQKnAt0C7QL2AwUDGwMvAzsDQwNLA1MDWQNiA2gDbwN0A3kDfgO5A8ID5wPtBAYECwQWBCkEMwQ8BE4EVQRcBGkEcQR5
BH8EhgSMBJEElgUPBS8FkQXYBiUGLwZdBqsG7QcFBzEHSAdZB2EHeweKB5AHnAelB7AHugfKB9MH4QfpB/UH/AgDCAkIDwhtCIYJ
Cwk3CaYKGQqJCo0K7AtJC10Lngv3DAIMVgxdDK8MxwzQDNUNIg1tDbYN/A5BDoIOtg7yDxcPIw8/D0YPSw96D58Pyg/YD/YQAhAe
EDMQUBBjEIUQphDFEM8Q7REJESQRKRFCEUgRXxFiEXgRjRGgEbMRxhHZEewR/hIPEiASMBJAEk8SXhJsEnISfxKMEpQSoBKsErcS
whLGEtAS2hLkEu4S+BMCEwoTExMcEyUTLhM3tB0Oi4seC4seiwuL4PcJix4LIR2LCxV4mHyZfh7rOQWLviEdQfcOBaV6eKh0G3R5
eG4f9z4WeJh8mX4e6zkFi74hHUH3DgWleniodBt0eXhuHw4VuB2FfoCFfBt9dJecH/euB/cN+xWWNjz7IHreHR6kd5KeGqXIlJuy
yYHjHQsVYatrtbStq7W0aa1iYWtpYh4O+xx8t/gvuAtAeElYOhr3JKIV5/cArdgeKwdgHQsV983c+80GDqEy91KXBbYHe4xPf6oa
+CQH+2d+BWAHoYrAimUa+1wHMR0LFZGKjpEbkI6HhE9oa0tmH6VfBfcX0Kzh5xqEHQ5XHfde9xwLpHcdC/sV+2Gx9xb3C9a594S1
eXejywtOUFlRHmaNW6qxGvfjB/tjfwULM9xQ0dnHtMq5HgvRrtXRkB9hBgtIak44fR8O+65DHQtsfXd3ZxsL6FMdC3BPvk0bC6H3
exX7KPIp9yge8Y/nua7iaZ4YVWNdVkIbIGzv5R/32gb3Nj3s+zCNHvshJ/sI+x4f94/3Z8cdC3h5mp2qsZSkjR/3Doz3XIT3QRrK
b6V4pB6copuYHp2VWawbqZylprBwo2ZZaGpoaR8L2h18Hfdo+yn3Nftq+3H7Jvsz+24e+AL33xX3SJn7TPsg+xl3+1v7QvtGffdb
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
owAAewAArgAAqwEAsAAArQAArwAAigAAsQAAtQAAsgIAuQAAtgIAmgAAugAAvgAAuwEAvwAAvQAAjQAAxAAAwQIAxQAAnQAAlQAA
ywAAyAEAzQAAygAAzAAAkAAAzgAA0gAAzwIA1gAA0wIApwAA1wAA2wAA2AEA3AAA2gAAnwAAkwAA4QAA3gIA4gAAogAA4wABijAA
kQABuw0AjAAAkgAByQ0AjgAAlAAB1wsAwAAA3QAB4xMAxgAB9wMAxwAA5AAB+wEAZQAB/TQAfgAAiAAAgQEAhAAAhwAAfwAAhgAC
MgMAbwAAiQAAQQAACAAAdQAAaQAAdwAAdgAAcAEAdAAAeQECNgEAawEAYwACOAAAmQABQAACOQ4AbQECSA0BrQIAAQAEAAcACgAN
AFYAagDXAYYBtQJzAoICwgMEA3cDmQOcA7ADzwPoBDcEbgTXBV4FoAY7BrYHBQeICAYIRQhdCIEIhQiqCSEJ1QnaCmIKZQpsCnAK
1grZCuAK5QrqC14LYQvIC8sL0Aw5DQgNCw0ODR0NIA1jDcYOTA5PDlIObw6NDqkOzQ7fDuwO/w9GD1EPZw9yD5IPwg/XD+gP/BAh
ECQQvBDNENIRRxG6EdMR5BIFEhoSYxJ6EvATCRMOE3MTiRPuFEAUhRSrFX0WDxbcFu0XShfTGBkYPBj3GQYZPxlxGXwZvhonGkga
WBqQGtUbKhvJHJodCx0bHSwdOh1mHYodoh2lHg8eFx45HkceYx5sHnUeiR6lHvUfVB9cH2Ifgh+YH7Ifuh/CH80f2R/rH/If9CB9
IIQgiyCuIN8hBSEvIVUheiGEIachxCHhIfMiASIdIlIi1yMFIwwjEyMkIzEjSyNzI4kjlyOwI84j0SPqJFwkfySaJL8k2yUIJSEl
ZSVtJXolhSWbJa8lxCXPJdsl6iYJJh4mUCZsJowmqybHJt4m8icXJzonRydUJ18nmifAJ/4oIChcKIcoyClGKWEpdCnnKfcqCSoh
KjoqUCpnKoMqoCq3KsIq6CsSKx8rfCv+LC0sNCw7LFYsdSyFLKcs0i0ALSwtXi1mLXMtji2yLcMt0C4+LpUu5y8ALxQvLy88L0ov
oDA5MEAwWjCKMLww3jDyMPkxBTEPMT4xezGpMbMxvzHXMgYyHDJBMlUyhjKfMr4y2DL5Mw8zWjNnM4QznjPFNEg0bjR+NKA1GDUg
NS01czWGNZE1njWvNig2qjbyN043kDfEN9A34zfvN/s4CDgUOCE4RzheOHk4mzjDONo44jjkOO85ADkZOTM5cDl4OYk5ozndOeU6
DzoeOj46SjplOnI6fzqLOqI6rzq7Ot468zsAOww7RDtqO4I7oDvWPCo8LDx6PMc83jzuPP89DT0aPSg9Tj1hPeg+ZT8gP9M/5j/5
QAZAIEBRQG5AiECgQSBB1UH3QhpCdkKHQqtCu0LKQuVDhEQvRL1FOEVrRclGEUZKRrRHEEcsRz5HakeZR81IeUj7SlBKqUr9S1ZL
qkv5TAZMCExlTINM1kz1TQ1NF000TUNNVfw/Dv1VDvw2Dvw2DvxOfPc7+N13Err3O/s59zQT0Lz5ERU3tPs9qPs7HqAGqfc7svc9
5Bq/cLZTVHVYWh4T4In8zRVesWW4ubGxuLllsV1eZWVdHg5aCov3JLn3JAPq+A8Vwx33gBbBHS2gdvdP2vcy2gGs+KoD9wr3TxVl
+08F0Qav908F9zMGZvtPBdEGsPdPBfcs2vsfBqn3MgX3AdowBrn3TwVFBlz7TwX7KAa1908FRQZf+08F+yw89xcGbfsyBSY8Bvdf
94EV9ysGbfsyBfssBg77MPsh90f4RXf3l8ESpPct+x7e9wfI3/cHPe4T7feCeRX7D8j3Dwf3DavuzvcQGvcV+wrJJbwe950HE+6k
xoRmH21sdWsaZKZzrb+srMDz+wfCNx65Tl0H+waHNzb7ERqJ+yvlefcCQgj7ogd1NZGqHxP1jqy4i8katnetXFVrXlr7C/cJZut8
Hsj3vhXAas5qjFEIS1JXSx4T7ftE+L8VzcG8yB77gwdUmk/DwBoO3IeoeHb39qR5pPd9psWkEpfk932tmYodE+/A+ByEChPfwL4d
E+/AkgoT38DTHQ73EXzU99Gu97C2ErH3Hov3BPcu7Mv3R2+wE/Wx90cV+w3zQvcG3MClsNQeacHDbsYb9wO75e0fZgZZgH1hUxtt
Vp6zcx/3DPdNBRPur6GrmbUbrvukaAe8t3lZY2xXZmUf+zj3fQXexeC28xrrLKU4+wJATvsBHoxSnFWkXQgT9SJPO1aP+woI9x7J
FRPtrJS/xaYe9037nfsYNvsK9wKJ9xQZ9wT4AxW3qbW5w6FZXFxjU1NtHm+wb8OJvggO/IlaCqn3JAP3EfgPFcEd+7P7Wvp6Adj3
FQPY98IV+2z3E/s390D7DR6rB/sA9x1K9yiO90UI90nI9yj3AfcjHqsH+z77EvsU+y+K+20IDvu7+1r6egH3Z/cVA/fo98IVivdt
+xT3L/s+9xIIawf3AfsjyPso+0kajvtFSvso+wD7HQhrB/dA9w33E/c392waDvtB+JGm91x3AfcL9w2Mw2CmmvcNA/cL+BoVaaFu
relc9yCiuR50ul77IOIbrKeirh/b+w2JuRr3LAajlbCdrnGfaR9LeDhQG7+0sLwasX+jYWh0dWceV7dlVxpQdN5NG2V5eWJ7lGij
H/cuBlr7DotFGg4o927iAfee4gP3nvduFfts4vds923i+233bTT7bftsNAcOpR0O+833YO0BrffZA633whUp99ntBw78P3z3U/s+
dhK391MTYLfbFVa1YcDAtrXAHhOgwwoO/D+RdvmEdwFh998DYXwV6Ab3gvmEBSwGDvsXfLz4/7oBpvc391n3NQOm9+oV+yLH+2v3
WvdeyPdm9yf3IE73bvtX+2FP+2P7Kx73N3oV9zyK9zTw7Iv7NPsr+xGL+0slKo33SPcDHg77MIu1+Lu5Afdp9xgD5SUK+Be1Jgd5
fpyfH/kGaQc8ZD93NIQIXfcFB52Ye3cf/GoHdHt1cx4O+0+L9w74pcEBv8T3cfcoA/fe+JsVPGhDWE8e+0z7b3Nrg3wIYfhSB5r3
ggVfBot3+whkHvuGir3I9xXqv7gZxr+3ytwa9w4qzPsF+wsqRvsRVZtOzbqnq7cezSeFsxrC06O136JUPh4O+1p8uffGwPecvRKn
30/j90X3GvsM9ygT8qf3LBX7DvNe9wH3CvcMyfcY7UvLMKceE+zPsMa43Rr3CCHCIzApVyVbp2i8saWlsx6+VpGnGqu4j6PepFBA
Wnw6SR5BBn+FeoKDj3iVH+cGE/LOmSdYO3FAK21Im7IfpsuVwxq2baNiU3ZhVx4O+1OLtfcWwQGZuvdh9xYD9zolCvfCtWcHdn2c
nR/q6sAr+HReB/vl/GQFRveQMAd4eXd1Hvs590wV92H3swX7swcO+118vPgEwO33FxKn3Hml92T3KxP0p/cmFfsB71ft9yX06vcp
9xcp6vsWXl+AeWEejMGMqZO9CIawrYmtG87CmsC4H5uel6WlGpaIjYcefmBng1obUECWkl0fE+yFjHyOhxp2+8sFgHh9eHQaeZiE
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
ivxgpwoONPthtvjps/ead4AdE/RHHRPsSx0T9Ewd91H5LiAKN/tht/cmwgrr9xT3afcrE+73gp8Vr3Wzf7eKCMAdE/bFHfupB32D
fHceZl/3r7dYBnmEn5cfgPf3FdKS9wrr6pf7C0UeQoqH+xAvGyl89xXPHw6Gi7X4SXf3d2kdA6H3vxU3B/f495IF2Qf7+/yNSh0O
/BrQHa730xUjB/eU95IF7Qf7mvyhsh0OagrFbR0o+mQgHftufLp0dvhatrf3XRLD1feH3BO89w+YHZr5eiAdRou8+Qq2upAK+3j3
tyAd+12LuvgSuJ73XUkK+1X3myAdfJr4aJb3iZ4G+1uSB7UK9xYLtZAMDPcWmZiYDA334RT5VRWwEwCsAgABAAQABwANABEAFQAZ
AB4AOQA9AFAAVQBaAJwAxwDVANkA3gD9ARQBNAE5AU0BYwFnAW0BdAF+AaQBqAGvAbUBvQHCAccBzAIpAn0CuwLXAtoC4ALmAvYC
+wMFAw4DGAMgAycDKwM0AzsDQwNKA1ADVQNaA18DZANvA3UDgAOrA68D4wPoA+8EIAQnBDQEQgRNBF4EZgRxBHoEgwSKBJIEmASf
BKYErQSzBLkEvgTYBOEE+AUYBScFPgVFBUkFUgVeBWMFaAVxBXcFtAXDBcwF0AYeBiYGKwZABkgGfQaCBocGjAbCBvYHKgdbB4sH
jweYB6MHvwfdCAIIBggQCDEIRwhbCGsIbgiJCJgIpwjACNAI5wj9CRIJHgkyCUQJVglcCW0JeAmACY8JngmkCbAJtQm9CcoJ1wnk
CewJ+AoECg0KFAofCioKNAo+CkgKUgpcCmQKbQp2Cn9GCg5JHQ73ItT3IgusCuAd8WodC7UVYQsVIx0pCrUVaB0HVQr4Jwf7YYMF
YKwHrpJ3dB/7wWMdC1lOHQuL4VYK0yQdKEAK+wkhHSj7XQUO9wn3MgvoYegSCyUK95yGHaPAixr3pAbD+xijTzSRb4oZYffhtQdw
hmeWfaj7rPkoGFYG+5z9BnpiZnRghhn34fiPFfcL+5wF+3oGC7sK+CYHvMKnuh6v+5++CvtP+/SI90Ma+GMHrK2Pyx6v+/tnB7bH
jW26Cguh+DcVsYevh2Ua+4UHC6t/HQv7P2wKC54W+SsGhwr9D1/gBpeXgX4f/OEHe3h/fB59Wot/GwuQjoeET2hrS2YfpV8F9xfQ
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
AHAAeQByAGkAZwBoAHQAIACpACAAMgAwADIANQAsACAAUwB0AGUAaQBuAGIAZQByAGcAIABNAGUAZABpAGEAIABUAGUAYwBoAG4A
bwBsAG8AZwBpAGUAcwAgAEcAbQBiAEgAIAAoAGgAdAB0AHAAOgAvAC8AdwB3AHcALgBzAHQAZQBpAG4AYgBlAHIAZwAuAG4AZQB0
AC8AKQAsACAAdwBpAHQAaAAgAFIAZQBzAGUAcgB2AGUAZAAgAEYAbwBuAHQAIABOAGEAbQBlACAAIgBBAGMAYQBkAGUAbQBpAGMA
bwAiAC4ACgAKAFQAaABpAHMAIABGAG8AbgB0ACAAUwBvAGYAdAB3AGEAcgBlACAAaQBzACAAbABpAGMAZQBuAHMAZQBkACAAdQBu
AGQAZQByACAAdABoAGUAIABTAEkATAAgAE8AcABlAG4AIABGAG8AbgB0ACAATABpAGMAZQBuAHMAZQAsACAAVgBlAHIAcwBpAG8A
bgAgADEALgAxAC4AIABUAGgAaQBzACAAbABpAGMAZQBuAHMAZQAgAGkAcwAgAGMAbwBwAGkAZQBkACAAYgBlAGwAbwB3ACwAIABh
AG4AZAAgAGkAcwAgAGEAbABzAG8AIABhAHYAYQBpAGwAYQBiAGwAZQAgAHcAaQB0AGgAIABhACAARgBBAFEAIABhAHQAOgAgAGgA
dAB0AHAAOgAvAC8AcwBjAHIAaQBwAHQAcwAuAHMAaQBsAC4AbwByAGcALwBPAEYATAAKAAoALQAtAC0ALQAtAC0ALQAtAC0ALQAt
AC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0A
LQAtAC0ALQAtAC0ALQAtAC0ALQAtAAoAUwBJAEwAIABPAFAARQBOACAARgBPAE4AVAAgAEwASQBDAEUATgBTAEUAIABWAGUAcgBz
AGkAbwBuACAAMQAuADEAIAAtACAAMgA2ACAARgBlAGIAcgB1AGEAcgB5ACAAMgAwADAANwAKAC0ALQAtAC0ALQAtAC0ALQAtAC0A
LQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAt
AC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAKAAoAUABSAEUAQQBNAEIATABFAAoAVABoAGUAIABnAG8AYQBsAHMAIABvAGYAIAB0AGgA
ZQAgAE8AcABlAG4AIABGAG8AbgB0ACAATABpAGMAZQBuAHMAZQAgACgATwBGAEwAKQAgAGEAcgBlACAAdABvACAAcwB0AGkAbQB1
AGwAYQB0AGUAIAB3AG8AcgBsAGQAdwBpAGQAZQAgAGQAZQB2AGUAbABvAHAAbQBlAG4AdAAgAG8AZgAgAGMAbwBsAGwAYQBiAG8A
cgBhAHQAaQB2AGUAIABmAG8AbgB0ACAAcAByAG8AagBlAGMAdABzACwAIAB0AG8AIABzAHUAcABwAG8AcgB0ACAAdABoAGUAIABm
AG8AbgB0ACAAYwByAGUAYQB0AGkAbwBuACAAZQBmAGYAbwByAHQAcwAgAG8AZgAgAGEAYwBhAGQAZQBtAGkAYwAgAGEAbgBkACAA
bABpAG4AZwB1AGkAcwB0AGkAYwAgAGMAbwBtAG0AdQBuAGkAdABpAGUAcwAsACAAYQBuAGQAIAB0AG8AIABwAHIAbwB2AGkAZABl
ACAAYQAgAGYAcgBlAGUAIABhAG4AZAAgAG8AcABlAG4AIABmAHIAYQBtAGUAdwBvAHIAawAgAGkAbgAgAHcAaABpAGMAaAAgAGYA
bwBuAHQAcwAgAG0AYQB5ACAAYgBlACAAcwBoAGEAcgBlAGQAIABhAG4AZAAgAGkAbQBwAHIAbwB2AGUAZAAgAGkAbgAgAHAAYQBy
AHQAbgBlAHIAcwBoAGkAcAAgAHcAaQB0AGgAIABvAHQAaABlAHIAcwAuAAoACgBUAGgAZQAgAE8ARgBMACAAYQBsAGwAbwB3AHMA
IAB0AGgAZQAgAGwAaQBjAGUAbgBzAGUAZAAgAGYAbwBuAHQAcwAgAHQAbwAgAGIAZQAgAHUAcwBlAGQALAAgAHMAdAB1AGQAaQBl
AGQALAAgAG0AbwBkAGkAZgBpAGUAZAAgAGEAbgBkACAAcgBlAGQAaQBzAHQAcgBpAGIAdQB0AGUAZAAgAGYAcgBlAGUAbAB5ACAA
YQBzACAAbABvAG4AZwAgAGEAcwAgAHQAaABlAHkAIABhAHIAZQAgAG4AbwB0ACAAcwBvAGwAZAAgAGIAeQAgAHQAaABlAG0AcwBl
AGwAdgBlAHMALgAgAFQAaABlACAAZgBvAG4AdABzACwAIABpAG4AYwBsAHUAZABpAG4AZwAgAGEAbgB5ACAAZABlAHIAaQB2AGEA
dABpAHYAZQAgAHcAbwByAGsAcwAsACAAYwBhAG4AIABiAGUAIABiAHUAbgBkAGwAZQBkACwAIABlAG0AYgBlAGQAZABlAGQALAAg
AHIAZQBkAGkAcwB0AHIAaQBiAHUAdABlAGQAIABhAG4AZAAvAG8AcgAgAHMAbwBsAGQAIAB3AGkAdABoACAAYQBuAHkAIABzAG8A
ZgB0AHcAYQByAGUAIABwAHIAbwB2AGkAZABlAGQAIAB0AGgAYQB0ACAAYQBuAHkAIAByAGUAcwBlAHIAdgBlAGQAIABuAGEAbQBl
AHMAIABhAHIAZQAgAG4AbwB0ACAAdQBzAGUAZAAgAGIAeQAgAGQAZQByAGkAdgBhAHQAaQB2AGUAIAB3AG8AcgBrAHMALgAgAFQA
aABlACAAZgBvAG4AdABzACAAYQBuAGQAIABkAGUAcgBpAHYAYQB0AGkAdgBlAHMALAAgAGgAbwB3AGUAdgBlAHIALAAgAGMAYQBu
AG4AbwB0ACAAYgBlACAAcgBlAGwAZQBhAHMAZQBkACAAdQBuAGQAZQByACAAYQBuAHkAIABvAHQAaABlAHIAIAB0AHkAcABlACAA
bwBmACAAbABpAGMAZQBuAHMAZQAuACAAVABoAGUAIAByAGUAcQB1AGkAcgBlAG0AZQBuAHQAIABmAG8AcgAgAGYAbwBuAHQAcwAg
AHQAbwAgAHIAZQBtAGEAaQBuACAAdQBuAGQAZQByACAAdABoAGkAcwAgAGwAaQBjAGUAbgBzAGUAIABkAG8AZQBzACAAbgBvAHQA
IABhAHAAcABsAHkAIAB0AG8AIABhAG4AeQAgAGQAbwBjAHUAbQBlAG4AdAAgAGMAcgBlAGEAdABlAGQAIAB1AHMAaQBuAGcAIAB0
AGgAZQAgAGYAbwBuAHQAcwAgAG8AcgAgAHQAaABlAGkAcgAgAGQAZQByAGkAdgBhAHQAaQB2AGUAcwAuAAoACgBEAEUARgBJAE4A
SQBUAEkATwBOAFMACgAiAEYAbwBuAHQAIABTAG8AZgB0AHcAYQByAGUAIgAgAHIAZQBmAGUAcgBzACAAdABvACAAdABoAGUAIABz
AGUAdAAgAG8AZgAgAGYAaQBsAGUAcwAgAHIAZQBsAGUAYQBzAGUAZAAgAGIAeQAgAHQAaABlACAAQwBvAHAAeQByAGkAZwBoAHQA
IABIAG8AbABkAGUAcgAoAHMAKQAgAHUAbgBkAGUAcgAgAHQAaABpAHMAIABsAGkAYwBlAG4AcwBlACAAYQBuAGQAIABjAGwAZQBh
AHIAbAB5ACAAbQBhAHIAawBlAGQAIABhAHMAIABzAHUAYwBoAC4AIABUAGgAaQBzACAAbQBhAHkACgBpAG4AYwBsAHUAZABlACAA
cwBvAHUAcgBjAGUAIABmAGkAbABlAHMALAAgAGIAdQBpAGwAZAAgAHMAYwByAGkAcAB0AHMAIABhAG4AZAAgAGQAbwBjAHUAbQBl
AG4AdABhAHQAaQBvAG4ALgAKAAoAIgBSAGUAcwBlAHIAdgBlAGQAIABGAG8AbgB0ACAATgBhAG0AZQAiACAAcgBlAGYAZQByAHMA
IAB0AG8AIABhAG4AeQAgAG4AYQBtAGUAcwAgAHMAcABlAGMAaQBmAGkAZQBkACAAYQBzACAAcwB1AGMAaAAgAGEAZgB0AGUAcgAg
AHQAaABlACAAYwBvAHAAeQByAGkAZwBoAHQAIABzAHQAYQB0AGUAbQBlAG4AdAAoAHMAKQAuAAoACgAiAE8AcgBpAGcAaQBuAGEA
bAAgAFYAZQByAHMAaQBvAG4AIgAgAHIAZQBmAGUAcgBzACAAdABvACAAdABoAGUAIABjAG8AbABsAGUAYwB0AGkAbwBuACAAbwBm
ACAARgBvAG4AdAAgAFMAbwBmAHQAdwBhAHIAZQAgAGMAbwBtAHAAbwBuAGUAbgB0AHMAIABhAHMAIABkAGkAcwB0AHIAaQBiAHUA
dABlAGQAIABiAHkAIAB0AGgAZQAgAEMAbwBwAHkAcgBpAGcAaAB0ACAASABvAGwAZABlAHIAKABzACkALgAKAAoAIgBNAG8AZABp
AGYAaQBlAGQAIABWAGUAcgBzAGkAbwBuACIAIAByAGUAZgBlAHIAcwAgAHQAbwAgAGEAbgB5ACAAZABlAHIAaQB2AGEAdABpAHYA
ZQAgAG0AYQBkAGUAIABiAHkAIABhAGQAZABpAG4AZwAgAHQAbwAsACAAZABlAGwAZQB0AGkAbgBnACwAIABvAHIAIABzAHUAYgBz
AHQAaQB0AHUAdABpAG4AZwAgAC0ALQAgAGkAbgAgAHAAYQByAHQAIABvAHIAIABpAG4AIAB3AGgAbwBsAGUAIAAtAC0AIABhAG4A
eQAgAG8AZgAgAHQAaABlACAAYwBvAG0AcABvAG4AZQBuAHQAcwAgAG8AZgAgAHQAaABlACAATwByAGkAZwBpAG4AYQBsACAAVgBl
AHIAcwBpAG8AbgAsACAAYgB5ACAAYwBoAGEAbgBnAGkAbgBnACAAZgBvAHIAbQBhAHQAcwAgAG8AcgAgAGIAeQAgAHAAbwByAHQA
aQBuAGcAIAB0AGgAZQAgAEYAbwBuAHQAIABTAG8AZgB0AHcAYQByAGUAIAB0AG8AIABhACAAbgBlAHcAIABlAG4AdgBpAHIAbwBu
AG0AZQBuAHQALgAKAAoAIgBBAHUAdABoAG8AcgAiACAAcgBlAGYAZQByAHMAIAB0AG8AIABhAG4AeQAgAGQAZQBzAGkAZwBuAGUA
cgAsACAAZQBuAGcAaQBuAGUAZQByACwAIABwAHIAbwBnAHIAYQBtAG0AZQByACwAIAB0AGUAYwBoAG4AaQBjAGEAbAAgAHcAcgBp
AHQAZQByACAAbwByACAAbwB0AGgAZQByACAAcABlAHIAcwBvAG4AIAB3AGgAbwAgAGMAbwBuAHQAcgBpAGIAdQB0AGUAZAAgAHQA
bwAgAHQAaABlACAARgBvAG4AdAAgAFMAbwBmAHQAdwBhAHIAZQAuAAoACgBQAEUAUgBNAEkAUwBTAEkATwBOACAAJgAgAEMATwBO
AEQASQBUAEkATwBOAFMACgBQAGUAcgBtAGkAcwBzAGkAbwBuACAAaQBzACAAaABlAHIAZQBiAHkAIABnAHIAYQBuAHQAZQBkACwA
IABmAHIAZQBlACAAbwBmACAAYwBoAGEAcgBnAGUALAAgAHQAbwAgAGEAbgB5ACAAcABlAHIAcwBvAG4AIABvAGIAdABhAGkAbgBp
AG4AZwAgAGEAIABjAG8AcAB5ACAAbwBmACAAdABoAGUAIABGAG8AbgB0ACAAUwBvAGYAdAB3AGEAcgBlACwAIAB0AG8AIAB1AHMA
ZQAsACAAcwB0AHUAZAB5ACwAIABjAG8AcAB5ACwAIABtAGUAcgBnAGUALAAgAGUAbQBiAGUAZAAsACAAbQBvAGQAaQBmAHkALAAg
AHIAZQBkAGkAcwB0AHIAaQBiAHUAdABlACwAIABhAG4AZAAgAHMAZQBsAGwAIABtAG8AZABpAGYAaQBlAGQAIABhAG4AZAAgAHUA
bgBtAG8AZABpAGYAaQBlAGQAIABjAG8AcABpAGUAcwAgAG8AZgAgAHQAaABlACAARgBvAG4AdAAgAFMAbwBmAHQAdwBhAHIAZQAs
ACAAcwB1AGIAagBlAGMAdAAgAHQAbwAgAHQAaABlACAAZgBvAGwAbABvAHcAaQBuAGcAIABjAG8AbgBkAGkAdABpAG8AbgBzADoA
CgAKADEAKQAgAE4AZQBpAHQAaABlAHIAIAB0AGgAZQAgAEYAbwBuAHQAIABTAG8AZgB0AHcAYQByAGUAIABuAG8AcgAgAGEAbgB5
ACAAbwBmACAAaQB0AHMAIABpAG4AZABpAHYAaQBkAHUAYQBsACAAYwBvAG0AcABvAG4AZQBuAHQAcwAsACAAaQBuACAATwByAGkA
ZwBpAG4AYQBsACAAbwByACAATQBvAGQAaQBmAGkAZQBkACAAVgBlAHIAcwBpAG8AbgBzACwAIABtAGEAeQAgAGIAZQAgAHMAbwBs
AGQAIABiAHkAIABpAHQAcwBlAGwAZgAuAAoACgAyACkAIABPAHIAaQBnAGkAbgBhAGwAIABvAHIAIABNAG8AZABpAGYAaQBlAGQA
IABWAGUAcgBzAGkAbwBuAHMAIABvAGYAIAB0AGgAZQAgAEYAbwBuAHQAIABTAG8AZgB0AHcAYQByAGUAIABtAGEAeQAgAGIAZQAg
AGIAdQBuAGQAbABlAGQALAAgAHIAZQBkAGkAcwB0AHIAaQBiAHUAdABlAGQAIABhAG4AZAAvAG8AcgAgAHMAbwBsAGQAIAB3AGkA
dABoACAAYQBuAHkAIABzAG8AZgB0AHcAYQByAGUALAAgAHAAcgBvAHYAaQBkAGUAZAAgAHQAaABhAHQAIABlAGEAYwBoACAAYwBv
AHAAeQAgAGMAbwBuAHQAYQBpAG4AcwAgAHQAaABlACAAYQBiAG8AdgBlACAAYwBvAHAAeQByAGkAZwBoAHQAIABuAG8AdABpAGMA
ZQAgAGEAbgBkACAAdABoAGkAcwAgAGwAaQBjAGUAbgBzAGUALgAgAFQAaABlAHMAZQAgAGMAYQBuACAAYgBlACAAaQBuAGMAbAB1
AGQAZQBkACAAZQBpAHQAaABlAHIAIABhAHMAIABzAHQAYQBuAGQALQBhAGwAbwBuAGUAIAB0AGUAeAB0ACAAZgBpAGwAZQBzACwA
IABoAHUAbQBhAG4ALQByAGUAYQBkAGEAYgBsAGUAIABoAGUAYQBkAGUAcgBzACAAbwByACAAaQBuACAAdABoAGUAIABhAHAAcABy
AG8AcAByAGkAYQB0AGUAIABtAGEAYwBoAGkAbgBlAC0AcgBlAGEAZABhAGIAbABlACAAbQBlAHQAYQBkAGEAdABhACAAZgBpAGUA
bABkAHMAIAB3AGkAdABoAGkAbgAgAHQAZQB4AHQAIABvAHIAIABiAGkAbgBhAHIAeQAgAGYAaQBsAGUAcwAgAGEAcwAgAGwAbwBu
AGcAIABhAHMAIAB0AGgAbwBzAGUAIABmAGkAZQBsAGQAcwAgAGMAYQBuACAAYgBlACAAZQBhAHMAaQBsAHkAIAB2AGkAZQB3AGUA
ZAAgAGIAeQAgAHQAaABlACAAdQBzAGUAcgAuAAoACgAzACkAIABOAG8AIABNAG8AZABpAGYAaQBlAGQAIABWAGUAcgBzAGkAbwBu
ACAAbwBmACAAdABoAGUAIABGAG8AbgB0ACAAUwBvAGYAdAB3AGEAcgBlACAAbQBhAHkAIAB1AHMAZQAgAHQAaABlACAAUgBlAHMA
ZQByAHYAZQBkACAARgBvAG4AdAAgAE4AYQBtAGUAKABzACkAIAB1AG4AbABlAHMAcwAgAGUAeABwAGwAaQBjAGkAdAAgAHcAcgBp
AHQAdABlAG4AIABwAGUAcgBtAGkAcwBzAGkAbwBuACAAaQBzACAAZwByAGEAbgB0AGUAZAAgAGIAeQAgAHQAaABlACAAYwBvAHIA
cgBlAHMAcABvAG4AZABpAG4AZwAgAEMAbwBwAHkAcgBpAGcAaAB0ACAASABvAGwAZABlAHIALgAgAFQAaABpAHMAIAByAGUAcwB0
AHIAaQBjAHQAaQBvAG4AIABvAG4AbAB5ACAAYQBwAHAAbABpAGUAcwAgAHQAbwAgAHQAaABlACAAcAByAGkAbQBhAHIAeQAgAGYA
bwBuAHQAIABuAGEAbQBlACAAYQBzACAAcAByAGUAcwBlAG4AdABlAGQAIAB0AG8AIAB0AGgAZQAgAHUAcwBlAHIAcwAuAAoACgA0
ACkAIABUAGgAZQAgAG4AYQBtAGUAKABzACkAIABvAGYAIAB0AGgAZQAgAEMAbwBwAHkAcgBpAGcAaAB0ACAASABvAGwAZABlAHIA
KABzACkAIABvAHIAIAB0AGgAZQAgAEEAdQB0AGgAbwByACgAcwApACAAbwBmACAAdABoAGUAIABGAG8AbgB0ACAAUwBvAGYAdAB3
AGEAcgBlACAAcwBoAGEAbABsACAAbgBvAHQAIABiAGUAIAB1AHMAZQBkACAAdABvACAAcAByAG8AbQBvAHQAZQAsACAAZQBuAGQA
bwByAHMAZQAgAG8AcgAgAGEAZAB2AGUAcgB0AGkAcwBlACAAYQBuAHkAIABNAG8AZABpAGYAaQBlAGQAIABWAGUAcgBzAGkAbwBu
ACwAIABlAHgAYwBlAHAAdAAgAHQAbwAgAGEAYwBrAG4AbwB3AGwAZQBkAGcAZQAgAHQAaABlACAAYwBvAG4AdAByAGkAYgB1AHQA
aQBvAG4AKABzACkAIABvAGYAIAB0AGgAZQAgAEMAbwBwAHkAcgBpAGcAaAB0ACAASABvAGwAZABlAHIAKABzACkAIABhAG4AZAAg
AHQAaABlACAAQQB1AHQAaABvAHIAKABzACkAIABvAHIAIAB3AGkAdABoACAAdABoAGUAaQByACAAZQB4AHAAbABpAGMAaQB0ACAA
dwByAGkAdAB0AGUAbgAgAHAAZQByAG0AaQBzAHMAaQBvAG4ALgAKAAoANQApACAAVABoAGUAIABGAG8AbgB0ACAAUwBvAGYAdAB3
AGEAcgBlACwAIABtAG8AZABpAGYAaQBlAGQAIABvAHIAIAB1AG4AbQBvAGQAaQBmAGkAZQBkACwAIABpAG4AIABwAGEAcgB0ACAA
bwByACAAaQBuACAAdwBoAG8AbABlACwAIABtAHUAcwB0ACAAYgBlACAAZABpAHMAdAByAGkAYgB1AHQAZQBkACAAZQBuAHQAaQBy
AGUAbAB5ACAAdQBuAGQAZQByACAAdABoAGkAcwAgAGwAaQBjAGUAbgBzAGUALAAgAGEAbgBkACAAbQB1AHMAdAAgAG4AbwB0ACAA
YgBlACAAZABpAHMAdAByAGkAYgB1AHQAZQBkACAAdQBuAGQAZQByACAAYQBuAHkAIABvAHQAaABlAHIAIABsAGkAYwBlAG4AcwBl
AC4AIABUAGgAZQAgAHIAZQBxAHUAaQByAGUAbQBlAG4AdAAgAGYAbwByACAAZgBvAG4AdABzACAAdABvACAAcgBlAG0AYQBpAG4A
IAB1AG4AZABlAHIAIAB0AGgAaQBzACAAbABpAGMAZQBuAHMAZQAgAGQAbwBlAHMAIABuAG8AdAAgAGEAcABwAGwAeQAgAHQAbwAg
AGEAbgB5ACAAZABvAGMAdQBtAGUAbgB0ACAAYwByAGUAYQB0AGUAZAAgAHUAcwBpAG4AZwAgAHQAaABlACAARgBvAG4AdAAgAFMA
bwBmAHQAdwBhAHIAZQAuAAoACgBUAEUAUgBNAEkATgBBAFQASQBPAE4ACgBUAGgAaQBzACAAbABpAGMAZQBuAHMAZQAgAGIAZQBj
AG8AbQBlAHMAIABuAHUAbABsACAAYQBuAGQAIAB2AG8AaQBkACAAaQBmACAAYQBuAHkAIABvAGYAIAB0AGgAZQAgAGEAYgBvAHYA
ZQAgAGMAbwBuAGQAaQB0AGkAbwBuAHMAIABhAHIAZQAgAG4AbwB0ACAAbQBlAHQALgAKAAoARABJAFMAQwBMAEEASQBNAEUAUgAK
AFQASABFACAARgBPAE4AVAAgAFMATwBGAFQAVwBBAFIARQAgAEkAUwAgAFAAUgBPAFYASQBEAEUARAAgACIAQQBTACAASQBTACIA
LAAgAFcASQBUAEgATwBVAFQAIABXAEEAUgBSAEEATgBUAFkAIABPAEYAIABBAE4AWQAgAEsASQBOAEQALAAgAEUAWABQAFIARQBT
AFMAIABPAFIAIABJAE0AUABMAEkARQBEACwAIABJAE4AQwBMAFUARABJAE4ARwAgAEIAVQBUACAATgBPAFQAIABMAEkATQBJAFQA
RQBEACAAVABPACAAQQBOAFkAIABXAEEAUgBSAEEATgBUAEkARQBTACAATwBGACAATQBFAFIAQwBIAEEATgBUAEEAQgBJAEwASQBU
AFkALAAgAEYASQBUAE4ARQBTAFMAIABGAE8AUgAgAEEAIABQAEEAUgBUAEkAQwBVAEwAQQBSACAAUABVAFIAUABPAFMARQAgAEEA
TgBEACAATgBPAE4ASQBOAEYAUgBJAE4ARwBFAE0ARQBOAFQAIABPAEYAIABDAE8AUABZAFIASQBHAEgAVAAsACAAUABBAFQARQBO
AFQALAAgAFQAUgBBAEQARQBNAEEAUgBLACwAIABPAFIAIABPAFQASABFAFIAIABSAEkARwBIAFQALgAgAEkATgAgAE4ATwAgAEUA
VgBFAE4AVAAgAFMASABBAEwATAAgAFQASABFACAAQwBPAFAAWQBSAEkARwBIAFQAIABIAE8ATABEAEUAUgAgAEIARQAgAEwASQBB
AEIATABFACAARgBPAFIAIABBAE4AWQAgAEMATABBAEkATQAsACAARABBAE0AQQBHAEUAUwAgAE8AUgAgAE8AVABIAEUAUgAgAEwA
SQBBAEIASQBMAEkAVABZACwAIABJAE4AQwBMAFUARABJAE4ARwAgAEEATgBZACAARwBFAE4ARQBSAEEATAAsACAAUwBQAEUAQwBJ
AEEATAAsACAASQBOAEQASQBSAEUAQwBUACwAIABJAE4AQwBJAEQARQBOAFQAQQBMACwAIABPAFIAIABDAE8ATgBTAEUAUQBVAEUA
TgBUAEkAQQBMACAARABBAE0AQQBHAEUAUwAsACAAVwBIAEUAVABIAEUAUgAgAEkATgAgAEEATgAgAEEAQwBUAEkATwBOACAATwBG
ACAAQwBPAE4AVABSAEEAQwBUACwAIABUAE8AUgBUACAATwBSACAATwBUAEgARQBSAFcASQBTAEUALAAgAEEAUgBJAFMASQBOAEcA
IABGAFIATwBNACwAIABPAFUAVAAgAE8ARgAgAFQASABFACAAVQBTAEUAIABPAFIAIABJAE4AQQBCAEkATABJAFQAWQAgAFQATwAg
AFUAUwBFACAAVABIAEUAIABGAE8ATgBUACAAUwBPAEYAVABXAEEAUgBFACAATwBSACAARgBSAE8ATQAgAE8AVABIAEUAUgAgAEQA
RQBBAEwASQBOAEcAUwAgAEkATgAgAFQASABFACAARgBPAE4AVAAgAFMATwBGAFQAVwBBAFIARQAuAEEAYwBhAGQAZQBtAGkAYwBv
AEIAbwBsAGQAVgBlAHIAcwBpAG8AbgAgADAALgA5ADAANQA7AFMATQBUAEcAOwBBAGMAYQBkAGUAbQBpAGMAbwAtAEIAbwBsAGQA
OwAyADAAMgA1ADsARgBMADgANAAyAEEAYwBhAGQAZQBtAGkAYwBvACAAQgBvAGwAZABWAGUAcgBzAGkAbwBuACAAMAAuADkAMAA1
AEEAYwBhAGQAZQBtAGkAYwBvAC0AQgBvAGwAZABTAHQAZQBpAG4AYgBlAHIAZwAgAE0AZQBkAGkAYQAgAFQAZQBjAGgAbgBvAGwA
bwBnAGkAZQBzACAARwBtAGIASABDAG8AcAB5AHIAaQBnAGgAdAAgAKkAIAAyADAAMgA1ACAAUwB0AGUAaQBuAGIAZQByAGcAIABN
AGUAZABpAGEAIABUAGUAYwBoAG4AbwBsAG8AZwBpAGUAcwAgAEcAbQBiAEgALgAgAFQAaABpAHMAIABmAG8AbgB0ACAAaQBzACAA
bABpAGMAZQBuAHMAZQBkACAAdQBuAGQAZQByACAAdABoAGUAIABTAEkATAAgAE8AcABlAG4AIABGAG8AbgB0ACAATABpAGMAZQBu
AHMAZQAgACgAaAB0AHQAcAA6AC8ALwBzAGMAcgBpAHAAdABzAC4AcwBpAGwALgBvAHIAZwAvAE8ARgBMACkALgBoAHQAdABwADoA
LwAvAHcAdwB3AC4AcwB0AGUAaQBuAGIAZQByAGcALgBuAGUAdAAvAGgAdAB0AHAAOgAvAC8AdwB3AHcALgBzAHQAZQBpAG4AYgBl
AHIAZwAuAG4AZQB0AC8AQwBvAHAAeQByAGkAZwBoAHQAIACpACAAMgAwADIANQAsACAAUwB0AGUAaQBuAGIAZQByAGcAIABNAGUA
ZABpAGEAIABUAGUAYwBoAG4AbwBsAG8AZwBpAGUAcwAgAEcAbQBiAEgAIAAoAGgAdAB0AHAAOgAvAC8AdwB3AHcALgBzAHQAZQBp
AG4AYgBlAHIAZwAuAG4AZQB0AC8AKQAsACAAdwBpAHQAaAAgAFIAZQBzAGUAcgB2AGUAZAAgAEYAbwBuAHQAIABOAGEAbQBlACAA
IgBBAGMAYQBkAGUAbQBpAGMAbwAiAC4ACgAKAFQAaABpAHMAIABGAG8AbgB0ACAAUwBvAGYAdAB3AGEAcgBlACAAaQBzACAAbABp
AGMAZQBuAHMAZQBkACAAdQBuAGQAZQByACAAdABoAGUAIABTAEkATAAgAE8AcABlAG4AIABGAG8AbgB0ACAATABpAGMAZQBuAHMA
ZQAsACAAVgBlAHIAcwBpAG8AbgAgADEALgAxAC4AIABUAGgAaQBzACAAbABpAGMAZQBuAHMAZQAgAGkAcwAgAGMAbwBwAGkAZQBk
ACAAYgBlAGwAbwB3ACwAIABhAG4AZAAgAGkAcwAgAGEAbABzAG8AIABhAHYAYQBpAGwAYQBiAGwAZQAgAHcAaQB0AGgAIABhACAA
RgBBAFEAIABhAHQAOgAgAGgAdAB0AHAAOgAvAC8AcwBjAHIAaQBwAHQAcwAuAHMAaQBsAC4AbwByAGcALwBPAEYATAAKAAoALQAt
AC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0A
LQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAtAAoAUwBJAEwAIABPAFAARQBOACAARgBPAE4AVAAgAEwASQBD
AEUATgBTAEUAIABWAGUAcgBzAGkAbwBuACAAMQAuADEAIAAtACAAMgA2ACAARgBlAGIAcgB1AGEAcgB5ACAAMgAwADAANwAKAC0A
LQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAt
AC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAtAC0ALQAKAAoAUABSAEUAQQBNAEIATABFAAoAVABoAGUAIABnAG8A
YQBsAHMAIABvAGYAIAB0AGgAZQAgAE8AcABlAG4AIABGAG8AbgB0ACAATABpAGMAZQBuAHMAZQAgACgATwBGAEwAKQAgAGEAcgBl
ACAAdABvACAAcwB0AGkAbQB1AGwAYQB0AGUAIAB3AG8AcgBsAGQAdwBpAGQAZQAgAGQAZQB2AGUAbABvAHAAbQBlAG4AdAAgAG8A
ZgAgAGMAbwBsAGwAYQBiAG8AcgBhAHQAaQB2AGUAIABmAG8AbgB0ACAAcAByAG8AagBlAGMAdABzACwAIAB0AG8AIABzAHUAcABw
AG8AcgB0ACAAdABoAGUAIABmAG8AbgB0ACAAYwByAGUAYQB0AGkAbwBuACAAZQBmAGYAbwByAHQAcwAgAG8AZgAgAGEAYwBhAGQA
ZQBtAGkAYwAgAGEAbgBkACAAbABpAG4AZwB1AGkAcwB0AGkAYwAgAGMAbwBtAG0AdQBuAGkAdABpAGUAcwAsACAAYQBuAGQAIAB0
AG8AIABwAHIAbwB2AGkAZABlACAAYQAgAGYAcgBlAGUAIABhAG4AZAAgAG8AcABlAG4AIABmAHIAYQBtAGUAdwBvAHIAawAgAGkA
bgAgAHcAaABpAGMAaAAgAGYAbwBuAHQAcwAgAG0AYQB5ACAAYgBlACAAcwBoAGEAcgBlAGQAIABhAG4AZAAgAGkAbQBwAHIAbwB2
AGUAZAAgAGkAbgAgAHAAYQByAHQAbgBlAHIAcwBoAGkAcAAgAHcAaQB0AGgAIABvAHQAaABlAHIAcwAuAAoACgBUAGgAZQAgAE8A
RgBMACAAYQBsAGwAbwB3AHMAIAB0AGgAZQAgAGwAaQBjAGUAbgBzAGUAZAAgAGYAbwBuAHQAcwAgAHQAbwAgAGIAZQAgAHUAcwBl
AGQALAAgAHMAdAB1AGQAaQBlAGQALAAgAG0AbwBkAGkAZgBpAGUAZAAgAGEAbgBkACAAcgBlAGQAaQBzAHQAcgBpAGIAdQB0AGUA
ZAAgAGYAcgBlAGUAbAB5ACAAYQBzACAAbABvAG4AZwAgAGEAcwAgAHQAaABlAHkAIABhAHIAZQAgAG4AbwB0ACAAcwBvAGwAZAAg
AGIAeQAgAHQAaABlAG0AcwBlAGwAdgBlAHMALgAgAFQAaABlACAAZgBvAG4AdABzACwAIABpAG4AYwBsAHUAZABpAG4AZwAgAGEA
bgB5ACAAZABlAHIAaQB2AGEAdABpAHYAZQAgAHcAbwByAGsAcwAsACAAYwBhAG4AIABiAGUAIABiAHUAbgBkAGwAZQBkACwAIABl
AG0AYgBlAGQAZABlAGQALAAgAHIAZQBkAGkAcwB0AHIAaQBiAHUAdABlAGQAIABhAG4AZAAvAG8AcgAgAHMAbwBsAGQAIAB3AGkA
dABoACAAYQBuAHkAIABzAG8AZgB0AHcAYQByAGUAIABwAHIAbwB2AGkAZABlAGQAIAB0AGgAYQB0ACAAYQBuAHkAIAByAGUAcwBl
AHIAdgBlAGQAIABuAGEAbQBlAHMAIABhAHIAZQAgAG4AbwB0ACAAdQBzAGUAZAAgAGIAeQAgAGQAZQByAGkAdgBhAHQAaQB2AGUA
IAB3AG8AcgBrAHMALgAgAFQAaABlACAAZgBvAG4AdABzACAAYQBuAGQAIABkAGUAcgBpAHYAYQB0AGkAdgBlAHMALAAgAGgAbwB3
AGUAdgBlAHIALAAgAGMAYQBuAG4AbwB0ACAAYgBlACAAcgBlAGwAZQBhAHMAZQBkACAAdQBuAGQAZQByACAAYQBuAHkAIABvAHQA
aABlAHIAIAB0AHkAcABlACAAbwBmACAAbABpAGMAZQBuAHMAZQAuACAAVABoAGUAIAByAGUAcQB1AGkAcgBlAG0AZQBuAHQAIABm
AG8AcgAgAGYAbwBuAHQAcwAgAHQAbwAgAHIAZQBtAGEAaQBuACAAdQBuAGQAZQByACAAdABoAGkAcwAgAGwAaQBjAGUAbgBzAGUA
IABkAG8AZQBzACAAbgBvAHQAIABhAHAAcABsAHkAIAB0AG8AIABhAG4AeQAgAGQAbwBjAHUAbQBlAG4AdAAgAGMAcgBlAGEAdABl
AGQAIAB1AHMAaQBuAGcAIAB0AGgAZQAgAGYAbwBuAHQAcwAgAG8AcgAgAHQAaABlAGkAcgAgAGQAZQByAGkAdgBhAHQAaQB2AGUA
cwAuAAoACgBEAEUARgBJAE4ASQBUAEkATwBOAFMACgAiAEYAbwBuAHQAIABTAG8AZgB0AHcAYQByAGUAIgAgAHIAZQBmAGUAcgBz
ACAAdABvACAAdABoAGUAIABzAGUAdAAgAG8AZgAgAGYAaQBsAGUAcwAgAHIAZQBsAGUAYQBzAGUAZAAgAGIAeQAgAHQAaABlACAA
QwBvAHAAeQByAGkAZwBoAHQAIABIAG8AbABkAGUAcgAoAHMAKQAgAHUAbgBkAGUAcgAgAHQAaABpAHMAIABsAGkAYwBlAG4AcwBl
ACAAYQBuAGQAIABjAGwAZQBhAHIAbAB5ACAAbQBhAHIAawBlAGQAIABhAHMAIABzAHUAYwBoAC4AIABUAGgAaQBzACAAbQBhAHkA
CgBpAG4AYwBsAHUAZABlACAAcwBvAHUAcgBjAGUAIABmAGkAbABlAHMALAAgAGIAdQBpAGwAZAAgAHMAYwByAGkAcAB0AHMAIABh
AG4AZAAgAGQAbwBjAHUAbQBlAG4AdABhAHQAaQBvAG4ALgAKAAoAIgBSAGUAcwBlAHIAdgBlAGQAIABGAG8AbgB0ACAATgBhAG0A
ZQAiACAAcgBlAGYAZQByAHMAIAB0AG8AIABhAG4AeQAgAG4AYQBtAGUAcwAgAHMAcABlAGMAaQBmAGkAZQBkACAAYQBzACAAcwB1
AGMAaAAgAGEAZgB0AGUAcgAgAHQAaABlACAAYwBvAHAAeQByAGkAZwBoAHQAIABzAHQAYQB0AGUAbQBlAG4AdAAoAHMAKQAuAAoA
CgAiAE8AcgBpAGcAaQBuAGEAbAAgAFYAZQByAHMAaQBvAG4AIgAgAHIAZQBmAGUAcgBzACAAdABvACAAdABoAGUAIABjAG8AbABs
AGUAYwB0AGkAbwBuACAAbwBmACAARgBvAG4AdAAgAFMAbwBmAHQAdwBhAHIAZQAgAGMAbwBtAHAAbwBuAGUAbgB0AHMAIABhAHMA
IABkAGkAcwB0AHIAaQBiAHUAdABlAGQAIABiAHkAIAB0AGgAZQAgAEMAbwBwAHkAcgBpAGcAaAB0ACAASABvAGwAZABlAHIAKABz
ACkALgAKAAoAIgBNAG8AZABpAGYAaQBlAGQAIABWAGUAcgBzAGkAbwBuACIAIAByAGUAZgBlAHIAcwAgAHQAbwAgAGEAbgB5ACAA
ZABlAHIAaQB2AGEAdABpAHYAZQAgAG0AYQBkAGUAIABiAHkAIABhAGQAZABpAG4AZwAgAHQAbwAsACAAZABlAGwAZQB0AGkAbgBn
ACwAIABvAHIAIABzAHUAYgBzAHQAaQB0AHUAdABpAG4AZwAgAC0ALQAgAGkAbgAgAHAAYQByAHQAIABvAHIAIABpAG4AIAB3AGgA
bwBsAGUAIAAtAC0AIABhAG4AeQAgAG8AZgAgAHQAaABlACAAYwBvAG0AcABvAG4AZQBuAHQAcwAgAG8AZgAgAHQAaABlACAATwBy
AGkAZwBpAG4AYQBsACAAVgBlAHIAcwBpAG8AbgAsACAAYgB5ACAAYwBoAGEAbgBnAGkAbgBnACAAZgBvAHIAbQBhAHQAcwAgAG8A
cgAgAGIAeQAgAHAAbwByAHQAaQBuAGcAIAB0AGgAZQAgAEYAbwBuAHQAIABTAG8AZgB0AHcAYQByAGUAIAB0AG8AIABhACAAbgBl
AHcAIABlAG4AdgBpAHIAbwBuAG0AZQBuAHQALgAKAAoAIgBBAHUAdABoAG8AcgAiACAAcgBlAGYAZQByAHMAIAB0AG8AIABhAG4A
eQAgAGQAZQBzAGkAZwBuAGUAcgAsACAAZQBuAGcAaQBuAGUAZQByACwAIABwAHIAbwBnAHIAYQBtAG0AZQByACwAIAB0AGUAYwBo
AG4AaQBjAGEAbAAgAHcAcgBpAHQAZQByACAAbwByACAAbwB0AGgAZQByACAAcABlAHIAcwBvAG4AIAB3AGgAbwAgAGMAbwBuAHQA
cgBpAGIAdQB0AGUAZAAgAHQAbwAgAHQAaABlACAARgBvAG4AdAAgAFMAbwBmAHQAdwBhAHIAZQAuAAoACgBQAEUAUgBNAEkAUwBT
AEkATwBOACAAJgAgAEMATwBOAEQASQBUAEkATwBOAFMACgBQAGUAcgBtAGkAcwBzAGkAbwBuACAAaQBzACAAaABlAHIAZQBiAHkA
IABnAHIAYQBuAHQAZQBkACwAIABmAHIAZQBlACAAbwBmACAAYwBoAGEAcgBnAGUALAAgAHQAbwAgAGEAbgB5ACAAcABlAHIAcwBv
AG4AIABvAGIAdABhAGkAbgBpAG4AZwAgAGEAIABjAG8AcAB5ACAAbwBmACAAdABoAGUAIABGAG8AbgB0ACAAUwBvAGYAdAB3AGEA
cgBlACwAIAB0AG8AIAB1AHMAZQAsACAAcwB0AHUAZAB5ACwAIABjAG8AcAB5ACwAIABtAGUAcgBnAGUALAAgAGUAbQBiAGUAZAAs
ACAAbQBvAGQAaQBmAHkALAAgAHIAZQBkAGkAcwB0AHIAaQBiAHUAdABlACwAIABhAG4AZAAgAHMAZQBsAGwAIABtAG8AZABpAGYA
aQBlAGQAIABhAG4AZAAgAHUAbgBtAG8AZABpAGYAaQBlAGQAIABjAG8AcABpAGUAcwAgAG8AZgAgAHQAaABlACAARgBvAG4AdAAg
AFMAbwBmAHQAdwBhAHIAZQAsACAAcwB1AGIAagBlAGMAdAAgAHQAbwAgAHQAaABlACAAZgBvAGwAbABvAHcAaQBuAGcAIABjAG8A
bgBkAGkAdABpAG8AbgBzADoACgAKADEAKQAgAE4AZQBpAHQAaABlAHIAIAB0AGgAZQAgAEYAbwBuAHQAIABTAG8AZgB0AHcAYQBy
AGUAIABuAG8AcgAgAGEAbgB5ACAAbwBmACAAaQB0AHMAIABpAG4AZABpAHYAaQBkAHUAYQBsACAAYwBvAG0AcABvAG4AZQBuAHQA
cwAsACAAaQBuACAATwByAGkAZwBpAG4AYQBsACAAbwByACAATQBvAGQAaQBmAGkAZQBkACAAVgBlAHIAcwBpAG8AbgBzACwAIABt
AGEAeQAgAGIAZQAgAHMAbwBsAGQAIABiAHkAIABpAHQAcwBlAGwAZgAuAAoACgAyACkAIABPAHIAaQBnAGkAbgBhAGwAIABvAHIA
IABNAG8AZABpAGYAaQBlAGQAIABWAGUAcgBzAGkAbwBuAHMAIABvAGYAIAB0AGgAZQAgAEYAbwBuAHQAIABTAG8AZgB0AHcAYQBy
AGUAIABtAGEAeQAgAGIAZQAgAGIAdQBuAGQAbABlAGQALAAgAHIAZQBkAGkAcwB0AHIAaQBiAHUAdABlAGQAIABhAG4AZAAvAG8A
cgAgAHMAbwBsAGQAIAB3AGkAdABoACAAYQBuAHkAIABzAG8AZgB0AHcAYQByAGUALAAgAHAAcgBvAHYAaQBkAGUAZAAgAHQAaABh
AHQAIABlAGEAYwBoACAAYwBvAHAAeQAgAGMAbwBuAHQAYQBpAG4AcwAgAHQAaABlACAAYQBiAG8AdgBlACAAYwBvAHAAeQByAGkA
ZwBoAHQAIABuAG8AdABpAGMAZQAgAGEAbgBkACAAdABoAGkAcwAgAGwAaQBjAGUAbgBzAGUALgAgAFQAaABlAHMAZQAgAGMAYQBu
ACAAYgBlACAAaQBuAGMAbAB1AGQAZQBkACAAZQBpAHQAaABlAHIAIABhAHMAIABzAHQAYQBuAGQALQBhAGwAbwBuAGUAIAB0AGUA
eAB0ACAAZgBpAGwAZQBzACwAIABoAHUAbQBhAG4ALQByAGUAYQBkAGEAYgBsAGUAIABoAGUAYQBkAGUAcgBzACAAbwByACAAaQBu
ACAAdABoAGUAIABhAHAAcAByAG8AcAByAGkAYQB0AGUAIABtAGEAYwBoAGkAbgBlAC0AcgBlAGEAZABhAGIAbABlACAAbQBlAHQA
YQBkAGEAdABhACAAZgBpAGUAbABkAHMAIAB3AGkAdABoAGkAbgAgAHQAZQB4AHQAIABvAHIAIABiAGkAbgBhAHIAeQAgAGYAaQBs
AGUAcwAgAGEAcwAgAGwAbwBuAGcAIABhAHMAIAB0AGgAbwBzAGUAIABmAGkAZQBsAGQAcwAgAGMAYQBuACAAYgBlACAAZQBhAHMA
aQBsAHkAIAB2AGkAZQB3AGUAZAAgAGIAeQAgAHQAaABlACAAdQBzAGUAcgAuAAoACgAzACkAIABOAG8AIABNAG8AZABpAGYAaQBl
AGQAIABWAGUAcgBzAGkAbwBuACAAbwBmACAAdABoAGUAIABGAG8AbgB0ACAAUwBvAGYAdAB3AGEAcgBlACAAbQBhAHkAIAB1AHMA
ZQAgAHQAaABlACAAUgBlAHMAZQByAHYAZQBkACAARgBvAG4AdAAgAE4AYQBtAGUAKABzACkAIAB1AG4AbABlAHMAcwAgAGUAeABw
AGwAaQBjAGkAdAAgAHcAcgBpAHQAdABlAG4AIABwAGUAcgBtAGkAcwBzAGkAbwBuACAAaQBzACAAZwByAGEAbgB0AGUAZAAgAGIA
eQAgAHQAaABlACAAYwBvAHIAcgBlAHMAcABvAG4AZABpAG4AZwAgAEMAbwBwAHkAcgBpAGcAaAB0ACAASABvAGwAZABlAHIALgAg
AFQAaABpAHMAIAByAGUAcwB0AHIAaQBjAHQAaQBvAG4AIABvAG4AbAB5ACAAYQBwAHAAbABpAGUAcwAgAHQAbwAgAHQAaABlACAA
cAByAGkAbQBhAHIAeQAgAGYAbwBuAHQAIABuAGEAbQBlACAAYQBzACAAcAByAGUAcwBlAG4AdABlAGQAIAB0AG8AIAB0AGgAZQAg
AHUAcwBlAHIAcwAuAAoACgA0ACkAIABUAGgAZQAgAG4AYQBtAGUAKABzACkAIABvAGYAIAB0AGgAZQAgAEMAbwBwAHkAcgBpAGcA
aAB0ACAASABvAGwAZABlAHIAKABzACkAIABvAHIAIAB0AGgAZQAgAEEAdQB0AGgAbwByACgAcwApACAAbwBmACAAdABoAGUAIABG
AG8AbgB0ACAAUwBvAGYAdAB3AGEAcgBlACAAcwBoAGEAbABsACAAbgBvAHQAIABiAGUAIAB1AHMAZQBkACAAdABvACAAcAByAG8A
bQBvAHQAZQAsACAAZQBuAGQAbwByAHMAZQAgAG8AcgAgAGEAZAB2AGUAcgB0AGkAcwBlACAAYQBuAHkAIABNAG8AZABpAGYAaQBl
AGQAIABWAGUAcgBzAGkAbwBuACwAIABlAHgAYwBlAHAAdAAgAHQAbwAgAGEAYwBrAG4AbwB3AGwAZQBkAGcAZQAgAHQAaABlACAA
YwBvAG4AdAByAGkAYgB1AHQAaQBvAG4AKABzACkAIABvAGYAIAB0AGgAZQAgAEMAbwBwAHkAcgBpAGcAaAB0ACAASABvAGwAZABl
AHIAKABzACkAIABhAG4AZAAgAHQAaABlACAAQQB1AHQAaABvAHIAKABzACkAIABvAHIAIAB3AGkAdABoACAAdABoAGUAaQByACAA
ZQB4AHAAbABpAGMAaQB0ACAAdwByAGkAdAB0AGUAbgAgAHAAZQByAG0AaQBzAHMAaQBvAG4ALgAKAAoANQApACAAVABoAGUAIABG
AG8AbgB0ACAAUwBvAGYAdAB3AGEAcgBlACwAIABtAG8AZABpAGYAaQBlAGQAIABvAHIAIAB1AG4AbQBvAGQAaQBmAGkAZQBkACwA
IABpAG4AIABwAGEAcgB0ACAAbwByACAAaQBuACAAdwBoAG8AbABlACwAIABtAHUAcwB0ACAAYgBlACAAZABpAHMAdAByAGkAYgB1
AHQAZQBkACAAZQBuAHQAaQByAGUAbAB5ACAAdQBuAGQAZQByACAAdABoAGkAcwAgAGwAaQBjAGUAbgBzAGUALAAgAGEAbgBkACAA
bQB1AHMAdAAgAG4AbwB0ACAAYgBlACAAZABpAHMAdAByAGkAYgB1AHQAZQBkACAAdQBuAGQAZQByACAAYQBuAHkAIABvAHQAaABl
AHIAIABsAGkAYwBlAG4AcwBlAC4AIABUAGgAZQAgAHIAZQBxAHUAaQByAGUAbQBlAG4AdAAgAGYAbwByACAAZgBvAG4AdABzACAA
dABvACAAcgBlAG0AYQBpAG4AIAB1AG4AZABlAHIAIAB0AGgAaQBzACAAbABpAGMAZQBuAHMAZQAgAGQAbwBlAHMAIABuAG8AdAAg
AGEAcABwAGwAeQAgAHQAbwAgAGEAbgB5ACAAZABvAGMAdQBtAGUAbgB0ACAAYwByAGUAYQB0AGUAZAAgAHUAcwBpAG4AZwAgAHQA
aABlACAARgBvAG4AdAAgAFMAbwBmAHQAdwBhAHIAZQAuAAoACgBUAEUAUgBNAEkATgBBAFQASQBPAE4ACgBUAGgAaQBzACAAbABp
AGMAZQBuAHMAZQAgAGIAZQBjAG8AbQBlAHMAIABuAHUAbABsACAAYQBuAGQAIAB2AG8AaQBkACAAaQBmACAAYQBuAHkAIABvAGYA
IAB0AGgAZQAgAGEAYgBvAHYAZQAgAGMAbwBuAGQAaQB0AGkAbwBuAHMAIABhAHIAZQAgAG4AbwB0ACAAbQBlAHQALgAKAAoARABJ
AFMAQwBMAEEASQBNAEUAUgAKAFQASABFACAARgBPAE4AVAAgAFMATwBGAFQAVwBBAFIARQAgAEkAUwAgAFAAUgBPAFYASQBEAEUA
RAAgACIAQQBTACAASQBTACIALAAgAFcASQBUAEgATwBVAFQAIABXAEEAUgBSAEEATgBUAFkAIABPAEYAIABBAE4AWQAgAEsASQBO
AEQALAAgAEUAWABQAFIARQBTAFMAIABPAFIAIABJAE0AUABMAEkARQBEACwAIABJAE4AQwBMAFUARABJAE4ARwAgAEIAVQBUACAA
TgBPAFQAIABMAEkATQBJAFQARQBEACAAVABPACAAQQBOAFkAIABXAEEAUgBSAEEATgBUAEkARQBTACAATwBGACAATQBFAFIAQwBI
AEEATgBUAEEAQgBJAEwASQBUAFkALAAgAEYASQBUAE4ARQBTAFMAIABGAE8AUgAgAEEAIABQAEEAUgBUAEkAQwBVAEwAQQBSACAA
UABVAFIAUABPAFMARQAgAEEATgBEACAATgBPAE4ASQBOAEYAUgBJAE4ARwBFAE0ARQBOAFQAIABPAEYAIABDAE8AUABZAFIASQBH
AEgAVAAsACAAUABBAFQARQBOAFQALAAgAFQAUgBBAEQARQBNAEEAUgBLACwAIABPAFIAIABPAFQASABFAFIAIABSAEkARwBIAFQA
LgAgAEkATgAgAE4ATwAgAEUAVgBFAE4AVAAgAFMASABBAEwATAAgAFQASABFACAAQwBPAFAAWQBSAEkARwBIAFQAIABIAE8ATABE
AEUAUgAgAEIARQAgAEwASQBBAEIATABFACAARgBPAFIAIABBAE4AWQAgAEMATABBAEkATQAsACAARABBAE0AQQBHAEUAUwAgAE8A
UgAgAE8AVABIAEUAUgAgAEwASQBBAEIASQBMAEkAVABZACwAIABJAE4AQwBMAFUARABJAE4ARwAgAEEATgBZACAARwBFAE4ARQBS
AEEATAAsACAAUwBQAEUAQwBJAEEATAAsACAASQBOAEQASQBSAEUAQwBUACwAIABJAE4AQwBJAEQARQBOAFQAQQBMACwAIABPAFIA
IABDAE8ATgBTAEUAUQBVAEUATgBUAEkAQQBMACAARABBAE0AQQBHAEUAUwAsACAAVwBIAEUAVABIAEUAUgAgAEkATgAgAEEATgAg
AEEAQwBUAEkATwBOACAATwBGACAAQwBPAE4AVABSAEEAQwBUACwAIABUAE8AUgBUACAATwBSACAATwBUAEgARQBSAFcASQBTAEUA
LAAgAEEAUgBJAFMASQBOAEcAIABGAFIATwBNACwAIABPAFUAVAAgAE8ARgAgAFQASABFACAAVQBTAEUAIABPAFIAIABJAE4AQQBC
AEkATABJAFQAWQAgAFQATwAgAFUAUwBFACAAVABIAEUAIABGAE8ATgBUACAAUwBPAEYAVABXAEEAUgBFACAATwBSACAARgBSAE8A
TQAgAE8AVABIAEUAUgAgAEQARQBBAEwASQBOAEcAUwAgAEkATgAgAFQASABFACAARgBPAE4AVAAgAFMATwBGAFQAVwBBAFIARQAu
AGgAdAB0AHAAOgAvAC8AcwBjAHIAaQBwAHQAcwAuAHMAaQBsAC4AbwByAGcALwBPAEYATAADAAAAAAAA/7UAMgAAAAAAAAAAAAAA
AAAAAAAAAAAAAAEAAAAMAAAAAAAAAAIADQACAIAAAQCBAIEAAgCCAJgAAQCZAJkAAgCaAJ8AAQCgAKAAAgChAOsAAQDsAO0AAgDu
AQkAAQEKAQsAAgEMAZwAAQGdAaAAAgGhAawAAQAAAAEAAAAKADYAUAACREZMVAAOTEFUTgAaAAQAAAAA//8AAQAAAAAAAWxhdG4A
CgAA//8AAQABAAJrZXJuAA5rZXJuABQAAAABAAAAAAABAAAAAQAEAAIACAACAAoG+gABBmQABAAAAEQAkgDYANgA5gDsARYA5gEc
ASoBPAFGAWwBegGUAZQBmgG4AcIBzAJGAtgC+gG4AxADHgG4A5wBwgRuBSQF5gYMBhYGIAYgBiABmgGaAZoBmgGaAZoBuAHCAbgD
EAMQAxADEAMQAxABwgHCAcIBwgXmBiAC+gXmBgwGKgZMBioBlAXmBiAGWgG4ABEAJP/uADf/7gA5/+4AOv/uADz/7gB7/+4AfP/u
AH3/7gB+/+4Af//uAID/7gCB/+4Al//uAS7/7gF7/+4Bfv/uAaL/7gADAAP/7gF8/+4Bf//uAAEAFP/ZAAoAE//BABT/sgAV/+EA
Fv/BABf/qgAY/7oAGf+yABr/yQAb/8EAHP/RAAEAFP/hAAMAE//wABT/4QAa/9EABAAU/9EAFf/hABn/8AAa/+EAAgAU/+kAFf/Z
AAkAE//RABT/2QAV/9kAFv/ZABf/ugAY/+EAGf/BABv/yQAc/+EAAwAU/+EAFf/pABr/4QAGABT/0QAV/+EAFv/pABj/8AAb//AA
HP/4AAEAA//uAAcAN//JADn/tgA6/7YAWf/uAFr/7gF8/7YBf/+2AAIAD//uABH/7gACAA//5wAR/+cAHgAP/4MAEf+DAET/tgBI
/8kATP/uAFL/yQBV/+4Amv+2AJv/tgCc/7YAnf+2AJ7/tgCf/7YAoP+2AKL/yQCj/8kApP/JAKX/yQCm//IAp//uAKj/8gCp/+4A
rP/JAK3/yQCu/8kAr//JALD/yQCy/8kA6//uAQv/yQAkAA//yQAR/8kAJP/uAET/7gBI/+4AUv/uAFj/7gB7/+4AfP/uAH3/7gB+
/+4Af//uAID/7gCB/+4Amv/uAJv/7gCc/+4Anf/uAJ7/7gCf/+4AoP/uAKL/7gCj/+4ApP/uAKX/7gCs/+4Arf/uAK7/7gCv/+4A
sP/uALL/7gCz/+4AtP/uALX/7gC2/+4BC//uAAgAWP/uAFz/5wCz/+4AtP/uALX/7gC2/+4At//nALn/5wAFADf/nAA5/5wAOv+2
AXz/nAF//5wAAwAP/+cAEf/nADcACgAfAA//agAR/2oAJP+2AET/yQBI/8kAUv/JAHv/tgB8/7YAff+2AH7/tgB//7YAgP+2AIH/
tgCa/8kAm//JAJz/yQCd/8kAnv/JAJ//yQCg/8kAov/JAKP/yQCk/8kApf/JAKz/yQCt/8kArv/JAK//yQCw/8kAsv/JAQv/yQA0
AA//nAAQ/4MAEf+cACT/yQAyAAoARP+2AEj/tgBM/+4AUv+2AFX/7gBY/+4Ae//JAHz/yQB9/8kAfv/JAH//yQCA/8kAgf/JAI0A
CgCOAAoAjwAKAJAACgCRAAoAkgAKAJr/7QCb/7YAnP/tAJ3/7QCe/7YAn//bAKD/tgCi/9sAo/+2AKT/2wCl/9sApv/uAKf/9wCo
/+4Aqf/uAKz/yACt/7YArv/IAK//tgCw/9sAsv+2ALP/8gC0/+4Atf/uALb/9wDr/+4BCgAKAQv/tgAtAA//gwAQ/5wAEf+DAB3/
2wAe/9sAJP+2AET/tgBI/7YATP/uAFL/tgBY/8kAe/+2AHz/tgB9/7YAfv+2AH//tgCA/7YAgf+2AJr/yACb/7YAnP/IAJ3/yACe
/9sAn//IAKD/tgCi/8gAo/+2AKT/tgCl/9sApv/uAKf/7gCo//cAqf/uAKz/tgCt/7YArv+2AK//tgCw/8gAsv+2ALP/yQC0/8kA
tf/JALb/yQDr/+4BC/+2ADAAD/+cABD/nAAR/5wAHf/JAB7/yQAk/7YARP+2AEj/tgBM/+4AUv+2AFj/2wBc/+cAe/+2AHz/tgB9
/7YAfv+2AH//tgCA/7YAgf+2AJr/tgCb/7YAnP+2AJ3/tgCe/8gAn/+2AKD/tgCi/7YAo/+2AKT/tgCl/7YApv/uAKf/7gCo/+4A
qf/uAKz/tgCt/7YArv+2AK//tgCw/8gAsv+2ALP/2wC0/9sAtf/bALb/5AC3/+cAuf/nAOv/7gEL/7YACQAP/5wAEP+DABH/nAAd
/+cAHv/nAKL/2ACl/9gArP/YALD/2AACAXwASwF/AEsAAgAP/7YAEf+2AAIAD/+cABH/nAAIACT/tgB7/7YAfP+2AH3/tgB+/7YA
f/+2AID/tgCB/7YAAwBH/+cAVv/nAar/5wACAXz/nAF//5wAAQBEAAMADwARABMAFAAVABYAFwAYABkAGgAbABwAHQAeACQAJgAn
ACkALQAuAC8AMQAyADMANgA3ADgAOQA6ADwASQBVAFkAWgBcAHsAfAB9AH4AfwCAAIIAiwCMAI0AjgCPAJAAkQCSAJMAlACVAJYA
lwC5APoBLgE1AXsBfAF+AX8BogGlAacBqQACAHQABAAAAJoA1AAFAAoAAAAAAAAAAAAAAAAAAAAAAAAAAAAA/+4AAAAAAAAAAAAA
AAAAAAAAAAD/pf+c/5z/7v+c/8kAAAAAAAAAAAAAAAAAAAAAAAAAAP/u/6X/7gAAAAAAAAAAAAAAAAAAAAD/tv/nAAEAEQAkAC8A
OAA8AHsAfAB9AH4AfwCAAJMAlACVAJYAlwD6AS4AAgAJACQAJAADAC8ALwAEADgAOAABADwAPAACAHsAgAADAJMAlgABAJcAlwAC
APoA+gAEAS4BLgACAAIAFwAkACQAAQA4ADgABwA8ADwACABEAEQAAgBIAEgAAwBMAEwABABSAFIABQBYAFgABgBcAFwACQB7AIEA
AQCTAJYABwCXAJcACACaAKAAAgCiAKUAAwCmAKkABACsALAABQCyALIABQCzALYABgC3ALcACQC5ALkACQDrAOsABAELAQsABQEu
AS4ACAABAAAACgBIAG4AA0RGTFQAFExBVE4AIGxhdG4AMgAEAAAAAP//AAEAAAAAAAFsYXRuAAoAAP//AAEAAQAEAAAAAP//AAEA
AgADbGlnYQAUbGlnYQAabGlnYQAgAAAAAQAAAAAAAQAAAAAAAQABAAIABgAOAAQAAAABABAABAAAAAEAKAABABoAAQAIAAIABgAM
AZ8AAgBMAaAAAgBPAAEAAQBJAAEAGgABAAgAAgAGAAwBnwACAEwBoAACAE8AAQABAEkAAAABAAAAAQ==
""".replace("\n", ""))
PANEL_FONTS = {"Academico-Regular.otf": ACADEMICO_REGULAR, "Academico-Bold.otf": ACADEMICO_BOLD}
ACADEMICO_LICENSE = """Copyright (c) 2017-2025 Steinberg Media Technologies GmbH.

This Font Software is licensed under the SIL Open Font License, Version 1.1.
This license is copied below, and is also available with a FAQ at:
http://scripts.sil.org/OFL


-----------------------------------------------------------
SIL OPEN FONT LICENSE Version 1.1 - 26 February 2007
-----------------------------------------------------------

PREAMBLE
The goals of the Open Font License (OFL) are to stimulate worldwide
development of collaborative font projects, to support the font creation
efforts of academic and linguistic communities, and to provide a free and
open framework in which fonts may be shared and improved in partnership
with others.

The OFL allows the licensed fonts to be used, studied, modified and
redistributed freely as long as they are not sold by themselves. The
fonts, including any derivative works, can be bundled, embedded, 
redistributed and/or sold with any software provided that any reserved
names are not used by derivative works. The fonts and derivatives,
however, cannot be released under any other type of license. The
requirement for fonts to remain under this license does not apply
to any document created using the fonts or their derivatives.

DEFINITIONS
"Font Software" refers to the set of files released by the Copyright
Holder(s) under this license and clearly marked as such. This may
include source files, build scripts and documentation.

"Reserved Font Name" refers to any names specified as such after the
copyright statement(s).

"Original Version" refers to the collection of Font Software components as
distributed by the Copyright Holder(s).

"Modified Version" refers to any derivative made by adding to, deleting,
or substituting -- in part or in whole -- any of the components of the
Original Version, by changing formats or by porting the Font Software to a
new environment.

"Author" refers to any designer, engineer, programmer, technical
writer or other person who contributed to the Font Software.

PERMISSION & CONDITIONS
Permission is hereby granted, free of charge, to any person obtaining
a copy of the Font Software, to use, study, copy, merge, embed, modify,
redistribute, and sell modified and unmodified copies of the Font
Software, subject to the following conditions:

1) Neither the Font Software nor any of its individual components,
in Original or Modified Versions, may be sold by itself.

2) Original or Modified Versions of the Font Software may be bundled,
redistributed and/or sold with any software, provided that each copy
contains the above copyright notice and this license. These can be
included either as stand-alone text files, human-readable headers or
in the appropriate machine-readable metadata fields within text or
binary files as long as those fields can be easily viewed by the user.

3) No Modified Version of the Font Software may use the Reserved Font
Name(s) unless explicit written permission is granted by the corresponding
Copyright Holder. This restriction only applies to the primary font name as
presented to the users.

4) The name(s) of the Copyright Holder(s) or the Author(s) of the Font
Software shall not be used to promote, endorse or advertise any
Modified Version, except to acknowledge the contribution(s) of the
Copyright Holder(s) and the Author(s) or with their explicit written
permission.

5) The Font Software, modified or unmodified, in part or in whole,
must be distributed entirely under this license, and must not be
distributed under any other license. The requirement for fonts to
remain under this license does not apply to any document created
using the Font Software.

TERMINATION
This license becomes null and void if any of the above conditions are
not met.

DISCLAIMER
THE FONT SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO ANY WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT
OF COPYRIGHT, PATENT, TRADEMARK, OR OTHER RIGHT. IN NO EVENT SHALL THE
COPYRIGHT HOLDER BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
INCLUDING ANY GENERAL, SPECIAL, INDIRECT, INCIDENTAL, OR CONSEQUENTIAL
DAMAGES, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
FROM, OUT OF THE USE OR INABILITY TO USE THE FONT SOFTWARE OR FROM
OTHER DEALINGS IN THE FONT SOFTWARE.
"""


LOGO_SVG = harmonarium_icon_svg(64, small=True)   # browser tab and window icon

# ---------------- control panel ----------------
PAGE = r"""<!doctype html>
<html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Harmonarium</title>
<link rel="icon" href="/logo.svg" type="image/svg+xml">
<script>try{var t=localStorage.getItem("harmonarium-theme");if(t==="dark"||t==="light")document.documentElement.dataset.theme=t;}catch(e){}</script>
<style>
:root{--bg:#f6f5f2;--card:#fff;--ink:#1d1d1f;--muted:#6b6b70;--line:#e3e1dc;
--accent:#2f6f5e;--accent-ink:#fff;--accent-soft:#e3efe9;--warn:#b7791f;--stop:#b23b3b;--track:#ecebe6}
@media (prefers-color-scheme:dark){:root:not([data-theme=light]){--bg:#151517;--card:#1f1f22;--ink:#ececee;
--muted:#9a9aa1;--line:#2e2e33;--accent:#5fb39b;--accent-ink:#0f1a17;--accent-soft:#1f3530;
--warn:#e0a84a;--stop:#e07070;--track:#2a2a2e}}:root[data-theme=dark]{--bg:#151517;--card:#1f1f22;--ink:#ececee;
--muted:#9a9aa1;--line:#2e2e33;--accent:#5fb39b;--accent-ink:#0f1a17;--accent-soft:#1f3530;
--warn:#e0a84a;--stop:#e07070;--track:#2a2a2e}
*{box-sizing:border-box}
body{margin:0;background:var(--bg);color:var(--ink);
font:15px/1.45 -apple-system,BlinkMacSystemFont,"Segoe UI",Roboto,sans-serif}
main{max-width:720px;margin:0 auto;padding:28px 16px 48px}
h1{font-size:22px;margin:0 0 4px}
.sub{color:var(--muted);margin:0 0 20px;font-size:14px}
.mono{font-family:ui-monospace,Menlo,Consolas,monospace}
.card{background:var(--card);border:1px solid var(--line);border-radius:12px;padding:18px;margin-bottom:14px}
h2{font-size:13px;color:var(--muted);text-transform:uppercase;letter-spacing:.05em;margin:0 0 12px}
.field{margin-bottom:18px}
.fhead{display:flex;justify-content:space-between;align-items:baseline;margin-bottom:6px}
.fhead strong{font-variant-numeric:tabular-nums}
.hint{color:var(--muted);font-size:13px}
input[type=range]{width:100%;accent-color:var(--accent)}
.chips{display:grid;grid-template-columns:repeat(6,1fr);gap:6px}
@media (max-width:480px){.chips{grid-template-columns:repeat(4,1fr)}}
.chip{position:relative}
.chip input{position:absolute;opacity:0;inset:0;margin:0;cursor:pointer}
.chip span{display:block;text-align:center;padding:8px 0;border:1px solid var(--line);border-radius:8px;
font:600 14px ui-monospace,Menlo,Consolas,monospace;user-select:none}
.chip input:checked + span{background:var(--accent);border-color:var(--accent);color:var(--accent-ink)}
.chip input:focus-visible + span{outline:2px solid var(--accent);outline-offset:2px}
.chip input:disabled{cursor:default}
.chip input:disabled:not(:checked) + span{opacity:.35}
.seg{display:flex;flex-wrap:wrap;gap:6px}
.seg label{position:relative}
.seg input{position:absolute;opacity:0;inset:0;margin:0;cursor:pointer}
.seg span{display:block;padding:8px 14px;border:1px solid var(--line);border-radius:8px;font-weight:600;font-size:14px;user-select:none}
.seg input:checked + span{background:var(--accent);border-color:var(--accent);color:var(--accent-ink)}
.seg input:focus-visible + span{outline:2px solid var(--accent);outline-offset:2px}
.seg .mono{font-family:ui-monospace,Menlo,Consolas,monospace}
#pitches span{padding:8px 10px}   /* five octave buttons on one line */
.two{display:grid;grid-template-columns:3fr 2fr;gap:18px}
@media (max-width:560px){.two{grid-template-columns:1fr}}
.rangerow{display:flex;gap:10px;align-items:center;margin-bottom:6px}
.rlabel{flex:0 0 42px;align-self:flex-start;padding-top:8px;color:var(--muted);font-size:13px}
.boxes{display:flex;flex-wrap:wrap;gap:4px}
.boxes input{width:44px;text-align:center;font:600 15px ui-monospace,Menlo,Consolas,monospace;padding:7px 2px;
border:1px solid var(--line);border-radius:6px;background:var(--card);color:var(--ink)}
.boxes input:focus{outline:2px solid var(--accent);outline-offset:1px}
.rangerow.bad .boxes input,.boxes input.invalid{border-color:var(--stop);
background:color-mix(in srgb,var(--stop) 14%,var(--card));box-shadow:0 0 0 1px var(--stop)}
.boxes input.nope{animation:nope .35s}
@keyframes nope{0%,100%{transform:none}25%{transform:translateX(-3px)}75%{transform:translateX(3px)}}
.rangetip{color:var(--muted);font-size:12px;margin-left:52px;min-height:1.3em}
.rangetip.warn{color:var(--stop)}
.smallbtn{font:600 12px -apple-system,BlinkMacSystemFont,"Segoe UI",Roboto,sans-serif;padding:3px 9px;
border-radius:6px;border:1px solid var(--line);background:var(--card);color:var(--accent);cursor:pointer;margin-left:6px}
.smallbtn[hidden]{display:none}
.lenwarn{color:var(--stop);font-weight:700;font-size:13px;margin-top:6px}
.lenwarn[hidden]{display:none}
.smallbtn:disabled{opacity:.4;cursor:default}
.rangewarn{display:none;color:var(--stop);font-weight:600;font-size:13px;margin-left:52px}
.rangewarn.show{display:block}
.linkbtn{background:none;border:0;padding:0;color:var(--accent);font:inherit;font-size:13px;font-weight:600;cursor:pointer}
.textin{width:100%;font:14px -apple-system,BlinkMacSystemFont,"Segoe UI",Roboto,sans-serif;padding:8px 10px;
border:1px solid var(--line);border-radius:8px;background:var(--bg);color:var(--ink)}
.fontstat{font-size:12px;margin-top:4px;min-height:1.3em;color:var(--muted)}
.fontstat.ok{color:var(--accent)} .fontstat.bad{color:var(--warn)}
.fontrow{display:flex;gap:12px;align-items:flex-start;flex-wrap:wrap}
.fontrow .textin{flex:1 1 220px;width:auto;min-width:0}
.outlinebox{flex:1 1 200px;font-size:14px;padding-top:7px}
.outlinewarn{display:block;font-size:12px;font-weight:600;color:var(--warn)}
.outlinebox .hint{display:block}
#outlinereq{display:block}
.outlinebox.forced{cursor:not-allowed}
.caution{margin-top:6px;padding:8px 10px;border-radius:8px;font-size:13px;font-weight:600;
background:#f5e3c8;color:#5a3b00}
@media (prefers-color-scheme:dark){:root:not([data-theme=light]) .caution{background:#3a2c14;color:#f0cf96}}:root[data-theme=dark] .caution{background:#3a2c14;color:#f0cf96}
.titlebar{display:flex;justify-content:space-between;align-items:flex-start;gap:12px}
.brand{display:flex;align-items:center;gap:14px}
.logo{width:58px;height:52px;flex:none}
.logo .s{stroke:var(--accent);stroke-width:3.5}
.logo .h{stroke:var(--bg);stroke-width:9}
.logo .n{fill:var(--ink)}
#quit{margin-top:4px}
.repeatopts{display:flex;flex-direction:column;gap:6px;margin-top:10px}
.presets{display:flex;flex-wrap:wrap;gap:6px;align-items:center}
.presets select,.presets input{font:14px -apple-system,BlinkMacSystemFont,"Segoe UI",Roboto,sans-serif;padding:7px 9px;
border:1px solid var(--line);border-radius:8px;background:var(--bg);color:var(--ink)}
.presets select{min-width:180px}
.presets input{flex:1;min-width:160px}
.diskwarn{color:var(--stop);font-weight:700;font-size:13px;margin-top:8px}
.diskwarn[hidden]{display:none}
.closed{max-width:520px;margin:80px auto;text-align:center;color:var(--muted)}
.engraverow{border-top:1px solid var(--line);margin-top:14px;padding-top:12px;display:flex;flex-direction:column;gap:8px}
.engravestat{color:var(--muted);font-size:13px;white-space:pre-wrap;overflow-wrap:anywhere}
.engravestat.bad{color:var(--stop)}
#previewframe{width:100%;height:900px;border:1px solid var(--line);border-radius:8px;background:#fff}
#previewcard[hidden]{display:none}
.previewnotes{font-size:13px;color:var(--muted);white-space:pre-wrap;margin-bottom:8px}
.previewnotes.bad{color:var(--stop)}
.footlinks{text-align:center;font-size:13px;margin-top:6px}
.footlinks a{color:var(--accent)}
.tick{display:flex;gap:8px;align-items:baseline;cursor:pointer}
.tick input{accent-color:var(--accent)}
.radios{display:flex;flex-direction:column;gap:8px}
.radios label{display:flex;gap:8px;align-items:baseline;cursor:pointer}
.radios input{accent-color:var(--accent)}
.path{font-family:ui-monospace,Menlo,Consolas,monospace;font-size:12px;color:var(--muted);word-break:break-all}
.pathrow{display:flex;gap:8px;margin-top:2px;padding-left:24px}
.pathrow input{flex:1;min-width:0;font:13px ui-monospace,Menlo,Consolas,monospace;padding:8px 10px;
border:1px solid var(--line);border-radius:8px;background:var(--bg);color:var(--ink)}
.pathrow button{padding:8px 14px}
details.adv{border-top:1px solid var(--line);margin:4px 0 16px;padding-top:12px}
details.adv summary{cursor:pointer;font-weight:600;color:var(--muted);font-size:14px}
details.adv[open] summary{margin-bottom:12px}
.enh{display:grid;grid-template-columns:repeat(4,1fr);gap:6px}
@media (max-width:480px){.enh{grid-template-columns:repeat(2,1fr)}}
.enh small{display:block;font-weight:400;font-family:-apple-system,BlinkMacSystemFont,"Segoe UI",Roboto,sans-serif;font-size:11px;opacity:.8}
.summary{background:var(--accent-soft);border-radius:8px;padding:10px 12px;font-size:14px}
.summary.big{background:#f5e3c8;color:#5a3b00}
@media (prefers-color-scheme:dark){:root:not([data-theme=light]) .summary.big{background:#3a2c14;color:#f0cf96}}:root[data-theme=dark] .summary.big{background:#3a2c14;color:#f0cf96}
.lock{color:var(--muted);font-size:13px;margin-top:10px;min-height:1.2em}
fieldset{border:0;padding:0;margin:0;min-width:0}
fieldset:disabled{opacity:.6}
.top{display:flex;justify-content:space-between;align-items:center;gap:12px;flex-wrap:wrap}
.pill{font-size:12px;font-weight:600;letter-spacing:.04em;text-transform:uppercase;
padding:4px 10px;border-radius:999px;background:var(--track);color:var(--muted)}
.pill.running,.pill.done{background:var(--accent);color:var(--accent-ink)}
.pill.paused{background:var(--warn);color:#1d1400}
.pill.stopped,.pill.error{background:var(--stop);color:#fff}
.btns{display:flex;gap:8px;flex-wrap:wrap;flex:1;justify-content:flex-end}
button{font:inherit;font-weight:600;border:1px solid var(--line);background:var(--card);color:var(--ink);
padding:9px 18px;border-radius:8px;cursor:pointer}
button:disabled{opacity:.4;cursor:default}
#start{background:var(--accent);border-color:var(--accent);color:var(--accent-ink)}
#stop:not(:disabled){color:var(--stop);border-color:var(--stop)}
#reset{color:var(--muted)}
.bar{height:12px;background:var(--track);border-radius:6px;overflow:hidden;margin:16px 0 6px}
.fill{height:100%;width:0;background:var(--accent);transition:width .2s}
.barline{display:flex;justify-content:space-between;color:var(--muted);font-size:13px;
font-variant-numeric:tabular-nums}
.stats{display:grid;grid-template-columns:repeat(auto-fit,minmax(140px,1fr));gap:12px;margin-top:14px}
.stat .k{font-size:12px;color:var(--muted);text-transform:uppercase;letter-spacing:.04em}
.stat .v{font-size:18px;font-weight:600;font-variant-numeric:tabular-nums;overflow-wrap:anywhere}
.card{min-width:0;overflow-wrap:anywhere}
h2 .mono{overflow-wrap:anywhere;word-break:break-all}
ul li{overflow-wrap:anywhere}
.msg{color:var(--muted);font-size:14px;margin-top:12px;min-height:1.4em;overflow-wrap:anywhere}
pre{margin:0;font:13px/1.6 ui-monospace,Menlo,Consolas,monospace;white-space:pre-wrap;overflow-wrap:anywhere;min-height:1.6em}
ul{margin:0;padding-left:18px;font:13px/1.7 ui-monospace,Menlo,Consolas,monospace;max-height:180px;overflow:auto}
.empty{color:var(--muted);font-size:14px}
/* ---- chords ---- */
:root{--logo:#111111;color-scheme:light}
@media (prefers-color-scheme:dark){:root:not([data-theme=light]){--logo:#ffffff;color-scheme:dark}}:root[data-theme=dark]{--logo:#ffffff;color-scheme:dark}
@font-face{font-family:"Academico";src:url("/fonts/Academico-Regular.otf") format("opentype");font-weight:400;font-style:normal;font-display:swap}
@font-face{font-family:"Academico";src:url("/fonts/Academico-Bold.otf") format("opentype");font-weight:700;font-style:normal;font-display:swap}
:root{--serif:"Academico",Georgia,"Times New Roman",serif}
.keyname,.chip.chord span,.tag,.boxes select,.tonicname,#recent{font-variant-numeric:lining-nums}
.logobtn{flex:none;padding:6px 8px;margin:-6px -8px;border:0;border-radius:10px;background:none;
color:var(--logo);cursor:pointer;line-height:0}
.logobtn:hover{background:var(--accent-soft)}
.logobtn:focus-visible{outline:2px solid var(--accent);outline-offset:2px}
.logo{display:block;height:92px;width:auto}
.vh{position:absolute;width:1px;height:1px;margin:-1px;padding:0;overflow:hidden;clip:rect(0 0 0 0);white-space:nowrap;border:0}
.brand{align-items:center;gap:22px}
.brand .sub{margin:0;max-width:40ch}
.titlebar{margin-bottom:18px;align-items:center}
.brand .winnote{margin:8px 0 0;max-width:60ch}
@media (max-width:640px){.titlebar{align-items:flex-start}.brand{flex-direction:column;align-items:flex-start;gap:12px}.logo{height:72px}}
select.sel{font:14px -apple-system,BlinkMacSystemFont,"Segoe UI",Roboto,sans-serif;padding:8px 10px;
border:1px solid var(--line);border-radius:8px;background:var(--bg);color:var(--ink);max-width:100%}
.keyrow{display:flex;flex-wrap:wrap;gap:8px;align-items:center}
.keyname{font:600 15px var(--serif);color:var(--muted)}
.extras{display:grid;grid-template-columns:repeat(auto-fill,minmax(210px,1fr));gap:8px 16px}
.extras .tick{font-size:14px}
.extras .hint{display:block;font-size:12px}
.extras .tick.off{opacity:.45}
.group{font-size:12px;color:var(--muted);text-transform:uppercase;letter-spacing:.05em;margin:14px 0 6px}
.group:first-child{margin-top:0}
.chordgrid{display:grid;grid-template-columns:repeat(auto-fill,minmax(88px,1fr));gap:6px}
.chip.chord span{padding:6px 4px;font:600 16px var(--serif);line-height:1.2}
.chip.chord small{display:block;font:400 11px -apple-system,BlinkMacSystemFont,"Segoe UI",Roboto,sans-serif;opacity:.8;margin-top:2px}
.chip.chord.tonic span{box-shadow:inset 0 -3px 0 var(--accent-soft)}
.addrow{display:flex;flex-wrap:wrap;gap:6px;align-items:center}
.addrow .slash{color:var(--muted);font-size:14px}
.customlist{display:flex;flex-wrap:wrap;gap:6px;margin-top:8px}
.customlist:empty{display:none}
.tag{display:inline-flex;gap:4px;align-items:center;padding:3px 4px 3px 10px;border:1px solid var(--line);
border-radius:999px;font:600 13px var(--serif)}
.tag button{padding:2px 8px;border:0;background:none;color:var(--muted);font:600 16px/1 -apple-system,BlinkMacSystemFont,"Segoe UI",Roboto,sans-serif}
.tag button:hover{color:var(--stop)}
.boxes select{font:600 14px var(--serif);padding:6px 4px;border:1px solid var(--line);
border-radius:6px;background:var(--card);color:var(--ink);min-width:64px;max-width:150px}
.rangerow.bad .boxes select{border-color:var(--stop);box-shadow:0 0 0 1px var(--stop)}
.frameopts{display:flex;flex-direction:column;gap:6px;margin-top:10px}
.tonicname{font:600 14px var(--serif)}
.crampwarn{margin:0 0 8px}
.footlinks{white-space:nowrap}
.legal{color:var(--muted);font-size:12px;text-align:center;margin:28px 0 8px;line-height:1.6}
.legal a{color:var(--muted)}
.help{display:inline-flex;align-items:center;justify-content:center;width:18px;height:18px;margin-left:6px;
border:1px solid var(--line);border-radius:50%;font:600 11px -apple-system,BlinkMacSystemFont,"Segoe UI",Roboto,sans-serif;
color:var(--muted);text-decoration:none;vertical-align:1px;letter-spacing:0}
.help:hover,.help:focus-visible{color:var(--accent);border-color:var(--accent)}
.winnote{margin:-12px 0 16px;font-size:12px;color:var(--muted);max-width:60ch}
#recent{font:14px/1.7 var(--serif)}
/* ---- layout: sections, folds, run column, dock ---- */
main{max-width:760px}
.layout{display:grid;gap:14px;align-items:start}
.colrun{display:flex;flex-direction:column;gap:14px;min-width:0}
.colrun .card{margin-bottom:0}
/* ---- settings: numbered collapsible cards ---- */
.colsettings fieldset{display:flex;flex-direction:column;gap:12px}
.presetbar{display:flex;align-items:center;gap:10px;flex-wrap:wrap;padding:0 2px 2px}
.presetlabel{font-size:14px;color:var(--muted)}
.presetbar .presets{flex:1;min-width:0}
details.acc{background:var(--card);border:1px solid var(--line);border-radius:12px;min-width:0}
summary.acchead{list-style:none;cursor:pointer;display:flex;align-items:center;gap:12px;padding:16px 20px;
border-radius:12px;min-width:0}
summary.acchead::-webkit-details-marker{display:none}
summary.acchead:focus-visible{outline:2px solid var(--accent);outline-offset:-2px}
details.acc[open]>summary.acchead{border-bottom:1px solid var(--line);border-radius:12px 12px 0 0}
.num{flex:none;width:24px;height:24px;border-radius:50%;display:inline-flex;align-items:center;justify-content:center;
background:var(--accent-soft);color:var(--accent);font:600 12px -apple-system,BlinkMacSystemFont,"Segoe UI",Roboto,sans-serif;
font-variant-numeric:tabular-nums}
.sech{margin:0;font-size:17px;font-weight:700;color:var(--ink);text-transform:none;letter-spacing:0;flex:none;
display:flex;align-items:center}
.ssum{flex:1;min-width:0;font-size:13px;color:var(--muted);text-transform:none;letter-spacing:0;font-weight:400;
white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
details.acc[open]>summary .ssum{visibility:hidden}
.chev{flex:none;width:9px;height:9px;margin:0 4px 4px 6px;border-right:2px solid var(--muted);border-bottom:2px solid var(--muted);
transform:rotate(45deg);transition:transform .15s}
details.acc[open]>summary .chev{transform:rotate(-135deg);margin-bottom:-4px}
summary.acchead:hover .chev{border-color:var(--ink)}
.accbody{padding:18px 20px 4px}
/* a sub-section inside a card: a divider across the card, then its own toggle */
details.sub{margin:4px -20px 0;padding:14px 20px 14px;border-top:1px solid var(--line)}
details.sub:last-child{margin-bottom:-4px}
details.sub>summary{cursor:pointer;display:flex;align-items:baseline;gap:12px;list-style:none;font-size:14px}
details.sub>summary::-webkit-details-marker{display:none}
.sublabel{color:var(--accent);font-weight:600;flex:none}
details.sub[open]>summary{margin-bottom:12px}
details.sub[open]>summary .ssum{display:none}
.runcard>.summary{margin:0 0 16px}
.runcard>.diskwarn{margin:-6px 0 14px}
.runcard>.lock:empty{display:none}
.runcard>.lock{margin:-8px 0 14px}
@media (max-width:560px){.ssum{display:none}}
.togglechips{display:flex;flex-wrap:wrap;gap:6px}
.togglechips .chip span{padding:7px 12px;font:600 13px -apple-system,BlinkMacSystemFont,"Segoe UI",Roboto,sans-serif}
.framerow{display:flex;flex-wrap:wrap;gap:10px 18px}
.framesel{display:flex;align-items:center;gap:8px;font-size:14px}
.framesel select{font:600 14px var(--serif);font-variant-numeric:lining-nums;min-width:120px}
.dock{position:fixed;left:0;right:0;bottom:0;z-index:5;background:var(--card);border-top:1px solid var(--line);
padding:10px 16px calc(10px + env(safe-area-inset-bottom, 0px));box-shadow:0 -4px 16px rgba(0,0,0,.06)}
.dockin{max-width:728px;margin:0 auto;display:flex;align-items:center;gap:10px}
.docksum{flex:1;min-width:0;font-size:13px;color:var(--muted);font-variant-numeric:tabular-nums;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
#dockstart{background:var(--accent);border-color:var(--accent);color:var(--accent-ink)}
body{padding-bottom:72px}
@media (min-width:1180px){
  main{max-width:1260px}
  .layout{grid-template-columns:minmax(0,1fr) 460px}
  .colrun{position:sticky;top:16px;max-height:calc(100vh - 32px);overflow:auto}
  .dock{display:none}
  body{padding-bottom:0}
}
</style></head><body><main>
<div class="titlebar">
  <div class="brand"><button type="button" class="logobtn" id="themetoggle" aria-label="Switch to dark mode" title="Switch to dark mode">@@LOGO@@</button><div><h1 class="vh">Harmonarium</h1>
  <p class="sub">Every ordering of the chords you pick, written as LilyPond scores.</p>
  <p class="winnote" id="winnote" hidden></p></div></div>
  <div style="text-align:right"><button type="button" id="quit" title="Save progress and close the app">Quit</button>
  <div class="footlinks"><a href="/guide" target="_blank" data-guide="">User guide</a> · <a href="/acknowledgements" target="_blank">Acknowledgements</a></div></div>
</div>

<div class="layout">
<div class="colsettings">
<fieldset id="settings">
    <div class="presetbar">
      <span class="presetlabel">Preset</span>
      <div class="presets">
        <select id="presetsel" aria-label="Saved presets"><option value="">Saved presets…</option></select>
        <button type="button" class="smallbtn" id="presetload">Load</button>
        <button type="button" class="smallbtn" id="presetdel">Delete</button>
        <input id="presetname" type="text" maxlength="60" placeholder="Name for the current settings" autocomplete="off">
        <button type="button" class="smallbtn" id="presetsave">Save</button>
      </div>
    </div>

    <details class="acc" id="d-chords" open>
      <summary class="acchead"><span class="num">1</span><h2 class="sech">Chords <a class="help" href="/guide#chords" target="_blank" data-guide="chords" aria-label="Help: Chords">?</a></h2><span class="ssum" id="chordssum"></span><span class="chev" aria-hidden="true"></span></summary>
      <div class="accbody">
      <div class="field">
        <div class="fhead"><span>Key</span><span class="keyname" id="keyname"></span></div>
        <div class="keyrow">
          <select class="sel" id="tonic" aria-label="Key note"></select>
          <select class="sel" id="mode" aria-label="Mode"></select>
        </div>
      </div>
      <div class="field">
        <div class="fhead"><span>Chord size</span><span class="hint">stacked in thirds from the key</span></div>
        <div class="seg" id="sizes"></div>
      </div>
      <div class="field">
        <div class="fhead"><span>More chords</span><span class="hint">hover for what each adds</span></div>
        <div class="togglechips" id="extras"></div>
      </div>
      <div class="field">
        <div class="fhead"><span>Chords to use</span><span><span class="hint" id="pickcount"></span><button type="button" class="smallbtn" id="pickkey">Key chords</button><button type="button" class="smallbtn" id="pickall">Select all</button><button type="button" class="smallbtn" id="picknone">Select none</button></span></div>
        <div id="chips"><span class="empty">Loading chords…</span></div>
      </div>
      <details class="sub" id="d-add">
        <summary><span class="sublabel">Add a chord by hand…</span><span class="ssum" id="addsum"></span></summary>
        <div class="addrow">
          <select class="sel" id="addroot" aria-label="Root"></select>
          <select class="sel" id="addquality" aria-label="Quality"></select>
          <span class="slash">over</span>
          <select class="sel" id="addbass" aria-label="Bass note (slash chord)"></select>
          <button type="button" class="smallbtn" id="addchord">Add</button>
        </div>
        <div class="customlist" id="customlist"></div>
      </details>
      </div>
    </details>

    <details class="acc" id="d-prog" open>
      <summary class="acchead"><span class="num">2</span><h2 class="sech">Progressions <a class="help" href="/guide#progressions" target="_blank" data-guide="progressions" aria-label="Help: Progressions">?</a></h2><span class="ssum" id="progsum"></span><span class="chev" aria-hidden="true"></span></summary>
      <div class="accbody">
      <div class="field">
        <div class="fhead"><label for="len">Chords per permutation</label><strong id="lenv">4</strong></div>
        <input type="range" id="len" min="2" max="12" step="1">
        <div class="lenwarn" id="lenwarn" hidden>Warning! File sizes get exponentially bigger beyond this point!</div>
        <div class="repeatopts">
          <label class="tick"><input type="checkbox" id="rm_norepeat">
            <span>No chord twice in a row <span class="hint">(I I V is skipped)</span></span></label>
          <label class="tick"><input type="checkbox" id="rm_once">
            <span>Use each chord once <span class="hint">(needs at least as many chords as the permutation is long)</span></span></label>
        </div>
      </div>
      <div class="field">
        <div class="fhead"><span>Start and end</span><span class="hint">added around every permutation; the repeat rules apply to the permuted chords only</span></div>
        <div class="framerow">
          <label class="framesel"><span>Start on</span><select class="sel" id="frame_start"></select></label>
          <label class="framesel"><span>End on</span><select class="sel" id="frame_end"></select></label>
        </div>
      </div>
      <details class="sub" id="d-range">
        <summary><span class="sublabel">Only part of the list…</span><span class="ssum" id="rangesum"></span></summary>
        <div class="fhead"><span class="hint" id="rangeinfo"></span><button type="button" class="smallbtn" id="fullrange" hidden>Reset to full range</button></div>
        <div class="rangerow" id="rstartrow"><span class="rlabel">Start</span><div class="boxes" id="rstart"></div></div>
        <div class="rangerow" id="rendrow"><span class="rlabel">End</span><div class="boxes" id="rend"></div></div>
        <div class="rangewarn" id="rangewarn">Permutation not possible — the ending must come after the starting permutation.</div>
        <div class="rangetip" id="rangetip">Pick a chord in each box to write only part of the full set.</div>
      </details>
      </div>
    </details>

    <details class="acc" id="d-score">
      <summary class="acchead"><span class="num">3</span><h2 class="sech">Score <a class="help" href="/guide#score" target="_blank" data-guide="score" aria-label="Help: Score">?</a></h2><span class="ssum" id="scoresum"></span><span class="chev" aria-hidden="true"></span></summary>
      <div class="accbody">
      <div class="two">
        <div class="field">
          <div class="fhead"><span>Labels</span><span class="hint">names above, numerals below</span></div>
          <div class="seg" id="labels"></div>
        </div>
        <div class="field">
          <div class="fhead"><span>Accidentals</span></div>
          <div class="seg" id="accidentals"></div>
        </div>
      </div>
      <div class="field">
        <div class="fhead"><span>Voicing</span><span class="hint">drop 2: 2nd from the top down an octave · open: every other note up an octave</span></div>
        <div class="seg" id="voicings"></div>
        <label class="tick" style="margin-top:8px"><input type="checkbox" id="double_bass">
          <span>Double the bass an octave below</span></label>
      </div>
      <div class="field">
        <div class="fhead"><span>Chord placement</span><span class="hint" id="placehint"></span></div>
        <div class="seg" id="placements"></div>
      </div>
      <div class="field">
        <div class="fhead"><span>Noteheads</span><span class="hint">look only: rhythm and time signature stay the same</span></div>
        <div class="seg" id="noteheads"></div>
      </div>
      <div class="two">
        <div class="field">
          <div class="fhead"><span>Clef</span></div>
          <div class="seg" id="clefs"></div>
        </div>
        <div class="field">
          <div class="fhead"><span>Octave</span><span class="hint">of the root or bass</span></div>
          <div class="seg" id="pitches"></div>
        </div>
      </div>
      <div class="field">
        <div class="fhead"><label for="staff">Staff size</label><strong id="staffv">20</strong></div>
        <input type="range" id="staff" min="10" max="30" step="1">
      </div>
      <div class="field">
        <label class="tick"><input type="checkbox" id="chunk_labels">
          <span>Chunk labels <span class="hint">(“I ii × ×” over the first measure of each group, to find your place in long runs)</span></span></label>
      </div>
      </div>
    </details>

    <details class="acc" id="d-pages">
      <summary class="acchead"><span class="num">4</span><h2 class="sech">Pages &amp; files <a class="help" href="/guide#pages-and-files" target="_blank" data-guide="pages-and-files" aria-label="Help: Pages and files">?</a></h2><span class="ssum" id="pagessum"></span><span class="chev" aria-hidden="true"></span></summary>
      <div class="accbody">
      <div class="field">
        <div class="fhead"><label for="firstsys">Systems on the first page <span class="hint">(under the title)</span></label><strong id="firstsysv">6</strong></div>
        <div class="caution crampwarn" id="firstcramp" hidden>More than 6 systems on the first page can look cramped: the title, subtitle and range line need room.</div>
        <input type="range" id="firstsys" min="1" max="12" step="1">
        <div class="lenwarn" id="firstsyswarn" hidden></div>
      </div>
      <div class="field">
        <div class="fhead"><label for="systems">Systems on the other pages</label><strong id="systemsv">8</strong></div>
        <div class="caution crampwarn" id="syscramp" hidden>More than 8 systems on a page can look cramped: chord names and numerals start to crowd the staves.</div>
        <input type="range" id="systems" min="1" max="12" step="1">
        <div class="lenwarn" id="syswarn" hidden></div>
      </div>
      <div class="two">
        <div class="field">
          <div class="fhead"><label for="ppdf">Pages per PDF</label><span class="hint">1–10,000</span></div>
          <input class="textin" id="ppdf" type="text" inputmode="numeric" maxlength="5" autocomplete="off" style="width:120px">
        </div>
        <div class="field">
          <div class="fhead"><label for="kb">Max file size</label><strong id="kbv">1000 KB</strong></div>
          <input type="range" id="kb" min="500" max="1500" step="50">
        </div>
      </div>
      <div class="field">
        <div class="fhead"><span>PDF links</span><span class="hint">clicking a chord opens its line in the .ly file; bigger PDFs</span></div>
        <div class="seg" id="pdflinks"></div>
      </div>
      <div class="field">
        <div class="fhead"><span>Save to</span></div>
        <div class="radios">
          <label><input type="radio" name="savemode" value="default">
            <span><span id="defaultplace">Next to this program</span> <span class="path" id="scriptdir"></span></span></label>
          <label><input type="radio" name="savemode" value="custom"><span>Another folder</span></label>
          <div class="pathrow">
            <input type="text" id="savepath" placeholder="Type a folder path or use Browse" spellcheck="false">
            <button type="button" id="browse">Browse…</button>
          </div>
        </div>
      </div>
      <div class="field">
        <label class="tick"><input type="checkbox" id="wtxt">
          <span>Also save plain-text lists <span class="hint">(.txt, one progression per line)</span></span></label>
      </div>
      </div>
    </details>

    <details class="acc" id="d-adv">
      <summary class="acchead"><span class="num">5</span><h2 class="sech">Advanced <a class="help" href="/guide#advanced-lilypond-and-fonts" target="_blank" data-guide="advanced-lilypond-and-fonts" aria-label="Help: Advanced">?</a></h2><span class="ssum" id="advsum"></span><span class="chev" aria-hidden="true"></span></summary>
      <div class="accbody">
      <div class="field">
        <div class="fhead"><label for="lppath">LilyPond program</label><span class="hint" id="lpstatus">looking for LilyPond…</span></div>
        <div class="presets">
          <input id="lppath" type="text" placeholder="Leave blank to find it automatically" spellcheck="false" autocomplete="off">
          <button type="button" class="smallbtn" id="lpuse">Use this</button>
          <button type="button" class="smallbtn" id="lpauto">Find automatically</button>
        </div>
        <div class="lenwarn" id="lpwarn" hidden></div>
      </div>
      <div class="field">
      <div class="fhead"><span>LilyPond version</span><span class="hint">the files are written in this version's syntax</span></div>
        <div class="seg" id="lpversions"></div>
      </div>
      <div class="field" style="margin-top:16px">
        <div class="fhead"><label for="textfont">Text font</label><span class="hint">blank = LilyPond's default</span></div>
        <input class="textin" id="textfont" list="fontlist" placeholder="Start typing a font name…" spellcheck="false" autocomplete="off">
        <datalist id="fontlist"></datalist>
        <div class="fontstat" id="textfontstat"></div>
      </div>
      <div class="field">
        <div class="fhead"><label for="musicfont">Music font</label><span class="hint">blank = Emmentaler (LilyPond's own)</span></div>
        <div class="fontrow">
          <input class="textin" id="musicfont" list="musicfontlist" placeholder="Pick from the list or type a name" spellcheck="false" autocomplete="off">
          <label class="tick outlinebox" id="outlinelabel"><input type="checkbox" id="outline"><span>Output music to outline
            <span class="hint">music symbols become shapes; text stays selectable</span>
            <span class="outlinewarn" id="outlinewarn"></span>
            <span class="hint" id="outlinereq" hidden></span></span></label>
        </div>
        <datalist id="musicfontlist"></datalist>
        <div class="fontstat" id="musicfontstat"></div>
        <div class="caution" id="musicwarn"></div>
        <div class="fontstat">Other music fonts must be installed in LilyPond's own fonts folder (see LilyPond's “Replacing the notation font”).</div>
      </div>
      </div>
    </details>
  </fieldset>
</div>
<div class="colrun">
<div class="card runcard">
  <div class="summary" id="summary"></div>
  <div class="diskwarn" id="diskwarn" hidden></div>
  <div class="lock" id="lock"></div>
  <div class="top">
    <span class="pill" id="pill">idle</span>
    <div class="btns">
      <button id="start">Start</button>
      <button id="pause">Pause</button>
      <button id="stop">Stop</button>
      <button id="reset">Reset</button>
    </div>
  </div>
  <div class="bar"><div class="fill" id="fill"></div></div>
  <div class="barline"><span id="pct">0%</span><span id="count">0 / 0</span></div>
  <div class="stats">
    <div class="stat"><div class="k">Elapsed</div><div class="v" id="elapsed">00:00:00</div></div>
    <div class="stat"><div class="k">Computing chunk</div><div class="v" id="chunk">–</div></div>
    <div class="stat"><div class="k">Files finished</div><div class="v" id="nfiles">0</div></div>
  </div>
  <div class="engraverow">
    <div class="btns" style="justify-content:flex-start">
      <button id="preview" title="Engrave the first page with the current settings and open it in a new tab">Preview first page</button>
      <button id="engrave" title="Engrave every finished score file into PDFs, one at a time">Engrave PDFs</button>
      <button id="engravestop">Stop engraving</button>
    </div>
    <div class="engravestat" id="engravestat"></div>
  </div>
  <div class="msg" id="msg"></div>
</div>

<div class="card" id="previewcard" hidden><h2>Preview · first page</h2>
  <div class="previewnotes" id="previewnotes"></div>
  <a id="previewlink" href="/preview.pdf" target="_blank" rel="noopener" hidden>Open the preview</a>
</div>
<div class="card"><h2>Latest progressions</h2><pre id="recent"></pre></div>
<div class="card"><h2>Finished files <span class="mono" id="outdir" style="text-transform:none;letter-spacing:0"></span></h2><div id="files"></div></div>
</div>
</div>
<div class="dock" id="dock" role="region" aria-label="Run">
  <div class="dockin">
    <span class="docksum" id="docksum"></span>
    <button type="button" id="dockpreview">Preview</button>
    <button type="button" id="dockstart">Start</button>
  </div>
</div>
<p class="legal">Harmonarium · Copyright © 2026 Joshua Nichols · Free software under the
<a href="/license/gpl" target="_blank">GNU GPL v3 or later</a>, with no warranty · Your scores are
<a href="/license/cc0" target="_blank">CC0</a> · <a href="/acknowledgements#license" target="_blank">License details</a> ·
<a href="https://github.com/joshdnichols/Harmonarium" target="_blank">Source code</a></p>
</main>
<script>
const $ = id => document.getElementById(id);
const pad = n => String(n).padStart(2, "0");
function fmtTime(s){ s = Math.floor(s); const d = Math.floor(s/86400); s %= 86400;
  const t = pad(Math.floor(s/3600)) + ":" + pad(Math.floor(s%3600/60)) + ":" + pad(s%60);
  return d ? d + "d " + t : t; }
function fmtBytes(b){ const u = ["bytes","KB","MB","GB","TB","PB","EB","ZB","YB"]; let i = 0;
  while (b >= 1000 && i < u.length-1){ b /= 1000; i++; }
  return (i ? b.toFixed(b < 10 ? 1 : 0) : Math.round(b)) + " " + u[i]; }
const JSONPOST = body => ({method: "POST", headers: {"Content-Type": "application/json"}, body: JSON.stringify(body)});

let OPT = null;                         // option lists from the program
let POOL = [], TONIC = null, KEYLABEL = "", poolFor = "", poolSeq = 0, pendingPick = null;
let draft = null, picked = [], status = "idle", locked = false;
let note = "", noteUntil = 0;
let FONTS = null, FONT_SOURCE = "";
function say(text){ note = text; noteUntil = Date.now() + 6000; $("msg").textContent = text; }
const byId = id => POOL.find(c => c.id === id);
function chordLabel(c){
  if (!c) return "?";
  return draft.labels === "names" ? c.name : draft.labels === "roman" ? c.roman : c.roman + " · " + c.name;
}

// ---- the chords to choose from (worked out by the program from key, size and extras) ----
function poolKey(){ return JSON.stringify([draft.key, draft.mode, draft.size, draft.extras, draft.custom]); }
async function loadPool(){
  const key = poolKey();
  if (key === poolFor) return;
  poolFor = key; const seq = ++poolSeq;
  // remember the ticked chords by place (group and position), so changing the key or the
  // chord size keeps "the 1st, 4th and 5th key chords" ticked even though their names change
  const placeOf = id => { const c = byId(id); if (!c) return null;
    const g = POOL.filter(x => x.group === c.group); return [c.group, g.indexOf(c)]; };
  const places = picked.map(placeOf);
  const framePlaces = [placeOf(draft.frame_start), placeOf(draft.frame_end)];
  let r;
  try { r = await (await fetch("/pool", JSONPOST({key: draft.key, mode: draft.mode, size: draft.size,
                                                  extras: draft.extras, custom: draft.custom}))).json(); }
  catch(e){ poolFor = ""; return; }
  if (seq !== poolSeq) return;          // a newer list is on its way
  const before = picked.slice();
  POOL = r.chords; TONIC = r.tonic; KEYLABEL = r.key_label;
  const ids = POOL.map(c => c.id);
  if (pendingPick){ picked = pendingPick.filter(id => ids.includes(id)); pendingPick = null; }
  else {
    const next = [];
    before.forEach((id, k) => {
      if (ids.includes(id)){ next.push(id); return; }
      const p = places[k]; if (!p) return;
      const g = POOL.filter(x => x.group === p[0]);
      if (g[p[1]]) next.push(g[p[1]].id);
    });
    picked = [...new Set(next)];
  }
  ["frame_start", "frame_end"].forEach((k, j) => {
    if (draft[k] === true) draft[k] = TONIC;              // older presets: true meant the tonic
    if (!draft[k] || ids.includes(draft[k])) return;
    const p = framePlaces[j], g = p ? POOL.filter(x => x.group === p[0]) : [];
    draft[k] = (p && g[p[1]]) ? g[p[1]].id : "";
  });
  if (pendingAdd){                       // tick the chord just added by hand
    pendingAdd = false;
    const hand = POOL.filter(c => c.group === "Added by hand");
    if (hand.length && !picked.includes(hand[hand.length - 1].id)) picked.push(hand[hand.length - 1].id);
  }
  buildChips(); renderSettings();
}

function buildChips(){
  const box = $("chips"); box.innerHTML = "";
  let group = null, grid = null;
  POOL.forEach(c => {
    if (c.group !== group){
      group = c.group;
      const h = document.createElement("div"); h.className = "group"; h.textContent = group;
      grid = document.createElement("div"); grid.className = "chordgrid";
      box.append(h, grid);
    }
    const l = document.createElement("label"); l.className = "chip chord" + (c.id === TONIC ? " tonic" : "");
    const input = document.createElement("input"); input.type = "checkbox"; input.value = c.id;
    input.setAttribute("aria-label", c.roman + " (" + c.name + ")");
    input.onchange = () => {
      if (input.checked) picked.push(c.id); else picked = picked.filter(x => x !== c.id);
      renderSettings();
    };
    const span = document.createElement("span");
    span.append(document.createTextNode(c.roman));
    const small = document.createElement("small"); small.textContent = c.name; span.appendChild(small);
    l.append(input, span); grid.appendChild(l);
  });
  if (!POOL.length) box.innerHTML = '<span class="empty">No chords.</span>';
  buildFrameMenus();
}

function buildSeg(boxId, name, options, onPick){
  const box = $(boxId); box.innerHTML = "";
  options.forEach(([value, label]) => {
    const l = document.createElement("label");
    const input = document.createElement("input");
    input.type = "radio"; input.name = name; input.value = value;
    input.onchange = () => { draft[name] = value; if (onPick) onPick(value); renderSettings(); };
    const span = document.createElement("span"); span.textContent = label;
    l.append(input, span); box.appendChild(l);
  });
}
function fillSelect(id, options){
  const sel = $(id); sel.innerHTML = "";
  options.forEach(([value, label]) => { const o = document.createElement("option"); o.value = value; o.textContent = label; sel.appendChild(o); });
}

function buildExtras(){
  const box = $("extras"); box.innerHTML = "";
  Object.entries(OPT.extras).forEach(([name, [label, hint]]) => {
    const l = document.createElement("label"); l.className = "chip"; l.dataset.extra = name; l.title = hint;
    const input = document.createElement("input"); input.type = "checkbox"; input.value = name;
    input.onchange = () => {
      draft.extras = input.checked ? draft.extras.concat(name) : draft.extras.filter(x => x !== name);
      renderSettings(); loadPool();
    };
    input.setAttribute("aria-label", label + ": " + hint);
    const span = document.createElement("span"); span.textContent = label;
    l.append(input, span); box.appendChild(l);
  });
}

function customLabel(c){
  const q = OPT.qualities[c.quality].split(" (")[0];
  return OPT.tonics[c.root] + (q === "Major" ? "" : q === "Minor" ? "m" : q === "Diminished" ? "dim"
         : q === "Augmented" ? "aug" : q === "Power chord" ? "5" : q) + (c.bass ? "/" + OPT.tonics[c.bass] : "");
}
function renderCustom(){
  const box = $("customlist"), key = JSON.stringify(draft.custom);
  if (box.dataset.key === key) return;
  box.dataset.key = key; box.innerHTML = "";
  draft.custom.forEach((c, k) => {
    const t = document.createElement("span"); t.className = "tag"; t.textContent = customLabel(c);
    const b = document.createElement("button"); b.type = "button"; b.textContent = "×";
    b.setAttribute("aria-label", "Remove " + customLabel(c));
    b.onclick = () => { draft.custom = draft.custom.filter((_, j) => j !== k); renderSettings(); loadPool(); };
    t.appendChild(b); box.appendChild(t);
  });
}
$("addchord").onclick = () => {
  const c = {root: $("addroot").value, quality: $("addquality").value, bass: $("addbass").value};
  if (draft.custom.some(x => x.root === c.root && x.quality === c.quality && x.bass === c.bass)){
    say(customLabel(c) + " is already in the list."); return; }
  draft.custom = draft.custom.concat(c);
  pendingAdd = true; renderSettings(); loadPool();
  say("Added " + customLabel(c) + " (ticked, under “Added by hand”).");
};
let pendingAdd = false;

function ordered(){ return POOL.map(c => c.id).filter(id => picked.includes(id)); }

// ---- range (start / end permutation): one menu per chord ----
let rangeKey = "", rangeBad = false, lastFull = true;
const isName = v => ordered().includes(v);
// Systems that fit on a letter page, measured with LilyPond 2.24 (7ths, names and numerals,
// 4 chords per measure) at staff sizes 18, 20 ... 30; odd sizes use the next even size up.
const SYSTEMS_FIT = {   // staff size: [root position first page, other pages, voice leading first, other]
  18: [11, 12, 11, 12], 20: [10, 11, 11, 11], 22: [9, 10, 10, 11], 24: [8, 9, 9, 10],
  26: [7, 8, 8, 9], 28: [7, 8, 7, 8], 30: [6, 7, 6, 7]};
// how many systems really fit, worked out by the program from the run's label heights
let FIT = null, fitKey = "", fitTimer = 0;
function requestFit(){
  clearTimeout(fitTimer);
  fitTimer = setTimeout(async () => {
    if (!picked.length || !estimate()) return;
    const body = settingsBody(), k = JSON.stringify(body);
    if (k === fitKey) return;
    fitKey = k;
    try {
      const r = await (await fetch("/fit", JSONPOST(body))).json();
      if (k !== fitKey) return;
      const was = JSON.stringify(FIT);
      FIT = r && r.ok ? r : null;
      if (JSON.stringify(FIT) !== was) renderSettings();
    } catch(e){}
  }, 250);
}
function maxSystemsPerPage(first){
  const size = Math.max(18, Math.min(30, draft.staff_size + draft.staff_size % 2));
  const row = SYSTEMS_FIT[size];
  return row[(draft.placement === "nearest" ? 2 : 0) + (first ? 0 : 1)];
}

// ---- permutation modes; exact whole-number (BigInt) counting ----
const RM = () => draft.repeat_mode || "all";
function fallingPow(n, k){ if (k > n) return 0n; let r = 1n; for (let j = 0n; j < k; j++) r *= (n - j); return r; }
function permCount(n, k, mode){
  n = BigInt(n); k = BigInt(k);
  if (mode === "once") return fallingPow(n, k);
  if (mode === "norepeat") return n * (n - 1n) ** (k - 1n);
  return n ** k;
}
function tailCount(n, k, j, mode){          // ways to finish once j chords are chosen
  if (mode === "once") return fallingPow(n - j, k - j);
  if (mode === "norepeat") return (n - 1n) ** (k - j);
  return n ** (k - j);
}
function rangeIndex(arr, chords){            // position in list order (same as the program)
  const mode = RM(), n = BigInt(chords.length), k = BigInt(arr.length);
  const avail = chords.map((_, x) => x);
  let i = 0n, prev = -1;
  arr.forEach((t, p) => {
    const d = chords.indexOf(t); let r = d;
    if (mode === "once"){ r = avail.indexOf(d); avail.splice(r, 1); }
    else if (mode === "norepeat"){ r = (prev < 0 || d < prev) ? d : d - 1; }
    i += BigInt(r) * tailCount(n, k, BigInt(p + 1), mode); prev = d;
  });
  return i;
}
function permAllowed(arr){
  if (RM() === "once") return new Set(arr).size === arr.length;
  if (RM() === "norepeat") return arr.every((t, p) => p === 0 || t !== arr[p - 1]);
  return true;
}
function firstPerm(chords, k){
  if (RM() === "once") return chords.slice(0, k);
  if (RM() === "norepeat") return Array.from({length: k}, (_, p) => chords[p % 2]);
  return Array(k).fill(chords[0]);
}
function lastPerm(chords, k){
  const n = chords.length;
  if (RM() === "once") return chords.slice(n - k).reverse();
  if (RM() === "norepeat") return Array.from({length: k}, (_, p) => chords[n - 1 - (p % 2)]);
  return Array(k).fill(chords[n - 1]);
}
function fullCount(){ return permCount(ordered().length, draft.length, RM()); }
function noPermReason(){
  return RM() === "once"
    ? "“Use each chord once” needs at least " + draft.length + " ticked chords (" + picked.length + " ticked)."
    : "“No chord twice in a row” needs at least 2 ticked chords.";
}
function fixRange(){
  const chords = ordered(), n = draft.length;
  if (!chords.length || fullCount() === 0n) return;
  const fit = (arr, fill) => Array.from({length: n}, (_, k) =>
    (arr && chords.includes(arr[k])) ? arr[k] : fill[k]);
  draft.rstart = fit(draft.rstart, firstPerm(chords, n));
  draft.rend = fit(draft.rend, lastPerm(chords, n));
}
function rangeIsFull(){
  const chords = ordered(), a = firstPerm(chords, draft.length), z = lastPerm(chords, draft.length);
  return draft.rstart.every((t, k) => t === a[k]) && draft.rend.every((t, k) => t === z[k]);
}
function menus(key){ return [...$(key).querySelectorAll("select")]; }
function buildRange(){
  const chords = ordered();
  rangeKey = draft.length + "|" + chords.join(",") + "|" + RM() + "|" + draft.labels;
  ["rstart", "rend"].forEach(key => {
    const el = $(key); el.innerHTML = "";
    for (let k = 0; k < draft.length; k++){
      const sel = document.createElement("select");
      sel.setAttribute("aria-label", (key === "rstart" ? "Start" : "End") + " chord " + (k + 1));
      chords.forEach(id => { const o = document.createElement("option"); o.value = id;
        o.textContent = chordLabel(byId(id)); sel.appendChild(o); });
      sel.onchange = () => { draft[key][k] = sel.value; renderSettings(); };
      el.appendChild(sel);
    }
  });
}
function renderRange(){
  const chords = ordered();
  if (!chords.length || fullCount() === 0n){
    $("rstart").innerHTML = $("rend").innerHTML = ""; rangeKey = ""; rangeBad = chords.length > 0;
    $("rstartrow").classList.remove("bad"); $("rendrow").classList.remove("bad");
    $("rangewarn").classList.remove("show"); $("rangeinfo").textContent = chords.length ? noPermReason() : "";
    $("fullrange").hidden = true;
    if (status !== "running") $("start").disabled = !locked && (rangeBad || !chords.length);
    return; }
  const key = draft.length + "|" + chords.join(",") + "|" + RM() + "|" + draft.labels;
  if (rangeKey !== key || !draft.rstart || !draft.rend){
    const sameChords = rangeKey.split("|").slice(0, 3).join("|") === key.split("|").slice(0, 3).join("|");
    if (rangeKey && !sameChords && lastFull){ draft.rstart = null; draft.rend = null; }  // full stays full
    fixRange(); buildRange();
  }
  ["rstart", "rend"].forEach(k => menus(k).forEach((sel, i) => { if (sel.value !== draft[k][i]) sel.value = draft[k][i]; }));
  const full = rangeIsFull();
  const a = rangeIndex(draft.rstart, chords), b = rangeIndex(draft.rend, chords);
  const badStart = !permAllowed(draft.rstart), badEnd = !permAllowed(draft.rend);
  const order = !badStart && !badEnd && !full && b <= a;
  rangeBad = badStart || badEnd || order;
  $("rstartrow").classList.toggle("bad", badStart);
  $("rendrow").classList.toggle("bad", badEnd || order);
  $("rangewarn").classList.toggle("show", rangeBad);
  $("rangewarn").textContent = (badStart || badEnd)
    ? "Permutation not possible — the " + (badStart ? "Start" : "End") + " permutation " +
      (RM() === "once" ? "uses a chord more than once." : "repeats a chord immediately.")
    : "Permutation not possible — the ending must come after the starting permutation.";
  $("fullrange").hidden = full;
  lastFull = full;
  if (status !== "running") $("start").disabled = !locked && rangeBad;
  const all = fullCount();
  $("rangeinfo").textContent = full ? "all permutations (" + all.toLocaleString() + ")"
    : rangeBad ? ""
    : "permutations " + (a + 1n).toLocaleString() + "–" + (b + 1n).toLocaleString()
      + " (" + (b - a + 1n).toLocaleString() + " of " + all.toLocaleString() + ")";
}
$("rm_norepeat").onchange = e => { draft.repeat_mode = e.target.checked ? "norepeat" : "all"; renderSettings(); };
$("rm_once").onchange = e => { draft.repeat_mode = e.target.checked ? "once" : "all"; renderSettings(); };
$("frame_start").onchange = e => { draft.frame_start = e.target.value; renderSettings(); };
$("frame_end").onchange = e => { draft.frame_end = e.target.value; renderSettings(); };
function buildFrameMenus(){
  ["frame_start", "frame_end"].forEach(id => {
    const sel = $(id); sel.innerHTML = "";
    const none = document.createElement("option"); none.value = ""; none.textContent = "— nothing —"; sel.appendChild(none);
    let group = null, og = null;
    POOL.forEach(c => {
      if (c.group !== group){ group = c.group; og = document.createElement("optgroup"); og.label = group; sel.appendChild(og); }
      const o = document.createElement("option"); o.value = c.id; o.textContent = chordLabel(c); og.appendChild(o);
    });
  });
  framesFor = draft.labels;
}
let framesFor = "";

// ---- free disk space on the save drive ----
let DISK = null, diskFor = null, diskTimer = 0;
function diskTarget(){ return draft.save_mode === "custom" ? draft.save_path.trim() : ""; }
function checkDisk(){
  const target = diskTarget(); if (target === diskFor) return;
  diskFor = target; clearTimeout(diskTimer);
  diskTimer = setTimeout(async () => {
    try { DISK = await (await fetch("/diskfree?path=" + encodeURIComponent(target))).json(); }
    catch(e){ DISK = null; }
    renderSettings();
  }, 400);
}
function renderDisk(e){
  checkDisk();
  const w = $("diskwarn");
  if (!e || !DISK || DISK.error || DISK.free === undefined){ w.hidden = true; return; }
  const need = e.bytes + (draft.write_txt ? e.txt : 0);
  w.hidden = need <= DISK.free * 0.9;
  w.textContent = "Not enough disk space: this run needs about " + fmtBytes(need) +
    " for its score" + (draft.write_txt ? " and text" : "") + " files (the PDFs need more), but only " +
    fmtBytes(DISK.free) + " is free on that drive.";
}

// ---- presets ----
let PRESETS = {};
const PRESET_KEYS = ["length","key","mode","size","extras","custom","labels","accidentals","frame_start","frame_end",
  "max_kb","staff_size","systems_per_page","first_page_systems","pages_per_pdf","text_font","music_font",
  "save_mode","save_path","write_txt","rstart","rend","clef","pitch","placement",
  "lilypond","repeat_mode","pdf_links","outline_fonts","noteheads","voicing","double_bass","chunk_labels"];
function fillPresets(){
  const sel = $("presetsel"), keep = sel.value;
  sel.innerHTML = '<option value="">Saved presets…</option>';
  Object.keys(PRESETS).sort((a, b) => a.localeCompare(b)).forEach(n => {
    const o = document.createElement("option"); o.value = o.textContent = n; sel.appendChild(o); });
  sel.value = PRESETS[keep] ? keep : "";
}
async function loadPresets(){ try { PRESETS = await (await fetch("/presets")).json(); } catch(e){ PRESETS = {}; } fillPresets(); }
async function postPresets(path, body){
  PRESETS = await (await fetch(path, JSONPOST(body))).json();
  fillPresets();
}
$("presetsave").onclick = async () => {
  const name = $("presetname").value.trim() || $("presetsel").value;
  if (!name){ say("Type a name for the preset first."); $("presetname").focus(); return; }
  if (PRESETS[name] && !confirm("Replace the saved preset “" + name + "”?")) return;
  const preset = {chords: ordered()};
  PRESET_KEYS.forEach(k => { preset[k] = JSON.parse(JSON.stringify(draft[k] === undefined ? null : draft[k])); });
  await postPresets("/presets", {name, preset});
  $("presetsel").value = name; $("presetname").value = ""; say("Saved preset “" + name + "”.");
};
$("presetload").onclick = () => {
  const name = $("presetsel").value, p = PRESETS[name];
  if (!p){ say("Choose a saved preset to load."); return; }
  PRESET_KEYS.forEach(k => { if (p[k] !== undefined && p[k] !== null) draft[k] = JSON.parse(JSON.stringify(p[k])); });
  draft.rstart = p.rstart ? p.rstart.slice() : null; draft.rend = p.rend ? p.rend.slice() : null;
  pendingPick = (p.chords || []).slice(); picked = pendingPick.slice();
  rangeKey = ""; lastFull = !p.rstart; poolFor = "";
  renderSettings(); loadPool(); say("Loaded preset “" + name + "”.");
};
$("presetdel").onclick = async () => {
  const name = $("presetsel").value;
  if (!name){ say("Choose a saved preset to delete."); return; }
  if (!confirm("Delete the preset “" + name + "”?")) return;
  await postPresets("/presets/delete", {name}); say("Deleted preset “" + name + "”.");
};

// ---- LilyPond: where it is, preview, engraving ----
let LP = null;
function renderLilypond(d){
  LP = d.lilypond || null;
  const st = $("lpstatus"), w = $("lpwarn");
  if (!LP){ st.textContent = "looking for LilyPond…"; w.hidden = true; return; }
  if (LP.error){ st.textContent = "not found"; w.hidden = false;
    w.textContent = "LilyPond wasn't found, so Preview and Engrave are off. Type the full path to the lilypond program above, or install LilyPond."; }
  else {
    st.textContent = "LilyPond " + LP.version + " (" + LP.source + ")";
    const is224 = LP.version.startsWith("2.24.");
    const mismatch = (is224 && draft.lilypond === "2.26") || (!is224 && draft.lilypond === "2.24");
    w.hidden = !mismatch;
    w.textContent = mismatch ? "This LilyPond is " + LP.version + ": choose “" + (is224 ? "2.24" : "2.26 or newer") +
      "” under LilyPond version above, or its files won't engrave." : "";
  }
  if (document.activeElement !== $("lppath") && !$("lppath").dataset.edited)
    $("lppath").value = (LP && LP.source === "your setting") ? LP.path : "";
}
$("lppath").oninput = () => { $("lppath").dataset.edited = "1"; };
async function setLilypond(path){
  say("Checking LilyPond…");
  const r = await (await fetch("/lilypond", JSONPOST({path}))).json();
  delete $("lppath").dataset.edited;
  say(r.error ? r.error : "Using LilyPond " + r.version + " (" + r.source + ").");
  poll();
}
$("lpuse").onclick = () => setLilypond($("lppath").value.trim());
$("lpauto").onclick = () => { $("lppath").value = ""; setLilypond(""); };

function renderEngrave(d){
  const e = d.engrave, s = $("engravestat");
  const haveLP = LP && !LP.error, busy = d.status === "running";
  $("preview").disabled = !haveLP || rangeBad || !estimate();
  $("engrave").disabled = !haveLP || busy || e.status === "running" || !d.file_total;
  $("engravestop").disabled = e.status !== "running";
  let text = "", bad = false;
  if (e.status === "running")
    text = "Engraving " + (e.done + 1) + " of " + e.total + ": " + e.current + "  ·  " + fmtTime(e.elapsed);
  else if (e.status === "done" || e.status === "stopped"){
    text = (e.status === "stopped" ? "Engraving stopped. " : "Engraving finished. ") + (e.done - e.skipped - e.failed_count) +
           " file(s) engraved" + (e.skipped ? ", " + e.skipped + " already up to date" : "") + ".";
  }
  if (e.failed_count){ bad = true;
    text += "\n" + e.failed_count + " file(s) had errors:" + e.failed.map(f =>
      "\n\n— " + f.file + (f.code != null ? "  (LilyPond exit code " + f.code + ")" : "") +
      (f.reasons || []).map(r => "\n   • " + r).join("") +
      (f.log ? "\n   Last lines from LilyPond:\n" + f.log.split("\n").map(l => "     " + l).join("\n") : "") +
      (f.logfile ? "\n   Full log: " + f.logfile + " (in the run folder)" : "")).join(""); }
  if (!haveLP) text = "Preview and Engrave need LilyPond (see Advanced).";
  s.textContent = text; s.classList.toggle("bad", bad);
}
$("engrave").onclick = () => send("engrave");
$("engravestop").onclick = () => send("engrave/stop");
// ---- dark / light: the logo switches; the default follows the system ----
const THEME_KEY = "harmonarium-theme", sysDark = matchMedia("(prefers-color-scheme: dark)");
const systemTheme = () => sysDark.matches ? "dark" : "light";
const shownTheme = () => document.documentElement.dataset.theme || systemTheme();
function labelThemeButton(){
  const text = "Switch to " + (shownTheme() === "dark" ? "light" : "dark") + " mode" +
    (document.documentElement.dataset.theme ? "" : " (now following your system)");
  $("themetoggle").setAttribute("aria-label", text); $("themetoggle").title = text;
}
function setTheme(t){                 // "dark", "light", or null to follow the system
  if (t) document.documentElement.dataset.theme = t; else delete document.documentElement.dataset.theme;
  try { if (t) localStorage.setItem(THEME_KEY, t); else localStorage.removeItem(THEME_KEY); } catch(e){}
  labelThemeButton();
}
$("themetoggle").onclick = () => {
  const next = shownTheme() === "dark" ? "light" : "dark";
  setTheme(next === systemTheme() ? null : next);   // back to the system's look = follow the system again
};
sysDark.addEventListener("change", labelThemeButton);
window.addEventListener("storage", e => { if (e.key === THEME_KEY){   // changed in the guide's window
  if (e.newValue) document.documentElement.dataset.theme = e.newValue; else delete document.documentElement.dataset.theme;
  labelThemeButton(); } });
labelThemeButton();
let WINDOWED = false;
// the guide: its own window in the app window, a new tab in a browser
document.addEventListener("click", async ev => {
  const a = ev.target.closest("a[data-guide]");
  if (!a) return;
  ev.stopPropagation();                              // a ? on a section heading doesn't fold it
  if (!WINDOWED) return;                             // browser: the link opens a new tab
  ev.preventDefault();
  try {
    const r = await (await fetch("/guide/open", JSONPOST({anchor: a.dataset.guide}))).json();
    if (!r.ok) window.open(a.href, "_blank");        // no second window: try a tab instead
  } catch(e){}
}, true);     // true in the app's own window: previews open in the PDF app
$("preview").onclick = async () => {
  const body = startBody();
  if (!body) return;
  if (WINDOWED) return previewInViewer(body);
  // open the tab now, while the click still counts (browsers block tabs opened later),
  // show a waiting note in it, then point it at the PDF once LilyPond has finished
  let tab = null;
  try { tab = window.open("", "_blank"); } catch(e){}
  if (tab){
    try {
      tab.document.title = "Engraving the preview…";
      tab.document.body.style.cssText = "margin:0;display:flex;align-items:center;justify-content:center;height:100vh;" +
        "font:16px -apple-system,BlinkMacSystemFont,'Segoe UI',Roboto,sans-serif;color:#6b6b70;background:#f6f5f2";
      tab.document.body.textContent = "Engraving the first page with LilyPond…";
    } catch(e){}
  }
  $("preview").disabled = true; $("previewcard").hidden = true;
  say("Engraving a preview of the first page…");
  try {
    const r = await (await fetch("/preview", JSONPOST(body))).json();
    const url = location.origin + "/preview.pdf?t=" + Date.now();
    const warn = r.warnings && r.warnings.length ? "LilyPond warnings:\n" + r.warnings.join("\n") : "";
    if (r.ok){
      if (tab && !tab.closed){ tab.location.href = url; say("Preview opened in a new tab."); }
      else { say("Your browser blocked the new tab: use the link below to open the preview."); }
      showPreviewNotes(warn, false, url, !tab || tab.closed);
    } else {
      if (tab && !tab.closed) tab.close();
      say("The preview failed: see below.");
      showPreviewNotes(r.error || "The preview failed.", true);
    }
  } catch(e){
    if (tab && !tab.closed) tab.close();
    say("Lost contact with the program while engraving the preview.");
  } finally { $("preview").disabled = false; }
};
async function previewInViewer(body){
  $("preview").disabled = true; $("previewcard").hidden = true;
  say("Engraving a preview of the first page…");
  try {
    const r = await (await fetch("/preview", JSONPOST(body))).json();
    const warn = r.warnings && r.warnings.length ? "LilyPond warnings:\n" + r.warnings.join("\n") : "";
    if (!r.ok){ say("The preview failed: see below."); showPreviewNotes(r.error || "The preview failed.", true); return; }
    const o = await (await fetch("/preview/open", {method: "POST"})).json();
    if (o.ok){ say("Preview opened in your PDF viewer."); showPreviewNotes(warn, false); }
    else { say("The preview is ready, but no PDF viewer opened: see below."); showPreviewNotes(o.error, true); }
  } catch(e){ say("Lost contact with the program while engraving the preview."); }
  finally { $("preview").disabled = false; }
}
// the card under the run controls only appears for warnings, errors or a blocked tab
function showPreviewNotes(text, bad, url, blocked){
  const card = $("previewcard"), notes = $("previewnotes"), link = $("previewlink");
  link.hidden = !url; if (url) link.href = url;
  link.textContent = blocked ? "Open the preview" : "Open the preview again";
  notes.textContent = text; notes.classList.toggle("bad", !!bad);
  card.hidden = !(text || blocked);
}

// ---- quit ----
$("quit").onclick = async () => {
  const busy = status === "running" || status === "paused";
  if (!confirm(busy ? "Stop this run (progress is saved) and quit Harmonarium?"
                    : "Quit Harmonarium?")) return;
  clearInterval(pollTimer);
  try { await fetch("/quit", {method: "POST"}); } catch(e){}
  document.querySelector("main").innerHTML =
    '<div class="closed"><h1>Harmonarium has closed.</h1><p>Progress is saved. You can close this tab.</p></div>';
};

$("pickall").onclick = () => { picked = POOL.map(c => c.id); renderSettings(); };
$("picknone").onclick = () => { picked = []; renderSettings(); };
$("pickkey").onclick = () => { picked = POOL.filter(c => c.group === "Key").map(c => c.id); renderSettings(); };
$("fullrange").onclick = () => { draft.rstart = null; draft.rend = null; renderSettings(); };

// measures per line: as the program works it out (fewer when labels are wide)
function barsPerSystem(chords, chars, staff){
  let bars = chords <= 2 ? 4 : chords <= 4 ? 2 : 1;
  const per = (chars * 5 + 6) * staff / 20;
  while (bars > 1 && bars * chords * per > 470) bars = Math.floor(bars / 2);
  return bars;
}
function estimate(){
  const chords = ordered(), k = chords.length, n = draft.length;
  if (!k || !POOL.length) return null;
  let total = permCount(k, n, RM());
  if (total === 0n) return null;
  if (draft.rstart && draft.rend && !rangeIsFull() && !rangeBad)
    total = rangeIndex(draft.rend, chords) - rangeIndex(draft.rstart, chords) + 1n;
  const count = Number(total);   // sizes only need to be approximate
  const L = draft.labels, cs = chords.map(byId);
  const fr = [draft.frame_start, draft.frame_end].filter(Boolean).map(byId).filter(Boolean);
  const frames = fr.length, m = n + frames;
  const avg = cs.reduce((s, c) => s + c.bytes[L], 0) / k;
  const perBar = 4 + n * avg + fr.reduce((s, c) => s + c.bytes[L], 0) + m + 1 + 3 + 7/4;
  const bytes = count * perBar * 1.03 + 2600;              // + chunk labels and headers
  const files = Math.max(1, Math.ceil(bytes / (draft.max_kb*1000 - 1000)));
  const textLen = c => (L === "names" ? c.name.length : L === "roman" ? c.roman.length : c.roman.length + c.name.length + 1);
  const avgText = cs.reduce((s, c) => s + textLen(c), 0) / k;
  const txt = count * (m * (avgText + 1) * 1.3 + 5);       // labels (♭ ♯ ° take 2-3 bytes), spaces, newline
  const txtFiles = Math.max(1, Math.ceil(txt / (draft.max_kb*1000)));
  const widest = Math.max(...cs.concat(fr).map(c => c.chars[L]));
  const bps = barsPerSystem(m, widest, draft.staff_size);
  const per = s => m >= 9 ? Math.max(1, Math.floor(s / 2)) : s * bps;   // measures per page
  const mpp = per(draft.systems_per_page), first = per(draft.first_page_systems);
  const book = first + mpp * (draft.pages_per_pdf - 1);              // measures per PDF
  const bookPages = x => x <= 0 ? 0 : 1 + Math.max(0, Math.ceil((x - first) / mpp));
  const pages = Math.floor(count / book) * draft.pages_per_pdf + bookPages(count % book);
  const pdfs = Math.max(files, Math.ceil(pages / draft.pages_per_pdf));
  return {total, bytes, files, txt, txtFiles, pages, pdfs};
}

function renderSettings(){
  if (!draft) return;
  renderCustom();
  document.querySelectorAll("input[name=savemode]").forEach(r => { r.checked = r.value === draft.save_mode; });
  if ($("savepath").value !== draft.save_path) $("savepath").value = draft.save_path;
  $("wtxt").checked = draft.write_txt;
  $("rm_norepeat").checked = RM() === "norepeat";
  $("rm_once").checked = RM() === "once";
  if (framesFor !== draft.labels && POOL.length) buildFrameMenus();
  $("frame_start").value = draft.frame_start || ""; $("frame_end").value = draft.frame_end || "";
  $("double_bass").checked = draft.double_bass; $("chunk_labels").checked = draft.chunk_labels;
  $("tonic").value = draft.key; $("mode").value = draft.mode;
  $("keyname").textContent = KEYLABEL;
  document.querySelectorAll("#extras input").forEach(cb => { cb.checked = draft.extras.includes(cb.value); });
  const big = !["triads", "sevenths"].includes(draft.size);
  const inv = document.querySelector('#extras [data-extra="inversions"]');
  if (inv) inv.classList.toggle("off", big);
  $("savepath").disabled = $("browse").disabled = locked || draft.save_mode !== "custom";
  $("len").value = draft.length; $("lenv").textContent = draft.length;
  $("lenwarn").hidden = draft.length <= 8;
  $("systems").value = draft.systems_per_page; $("systemsv").textContent = draft.systems_per_page;
  $("firstsys").value = draft.first_page_systems; $("firstsysv").textContent = draft.first_page_systems;
  const tooMany = (el, wanted, fit, where) => {
    $(el).hidden = wanted <= fit;
    $(el).textContent = FIT
      ? "Only " + fit + " system" + (fit > 1 ? "s" : "") + " fit on " + where + " with these chords, " +
        "voicing, labels and staff size, so the scores will use " + fit + "."
      : "Warning! At staff size " + draft.staff_size + ", only about " + fit +
        " system" + (fit > 1 ? "s" : "") + " fit on " + where + ". (Estimate.)";
  };
  $("firstcramp").hidden = draft.first_page_systems <= 6;
  $("syscramp").hidden = draft.systems_per_page <= 8;
  tooMany("firstsyswarn", draft.first_page_systems, FIT ? FIT.first : maxSystemsPerPage(true), "the first page, under the title");
  tooMany("syswarn", draft.systems_per_page, FIT ? FIT.rest : maxSystemsPerPage(false), "each of the other pages");
  requestFit();
  if (document.activeElement !== $("ppdf")) $("ppdf").value = draft.pages_per_pdf;
  $("ppdf").disabled = locked;
  if ($("textfont").value !== draft.text_font) $("textfont").value = draft.text_font;
  if ($("musicfont").value !== draft.music_font) $("musicfont").value = draft.music_font;
  $("textfont").disabled = $("musicfont").disabled = locked;
  renderFontStatus();
  $("staff").value = draft.staff_size;
  $("staffv").textContent = draft.staff_size + (draft.staff_size === 20 ? " (default)" : "");
  $("kb").value = draft.max_kb; $("kbv").textContent = draft.max_kb.toLocaleString() + " KB";
  document.querySelectorAll("#chips input").forEach(cb => { cb.checked = picked.includes(cb.value); });
  const segs = {sizes: "size", labels: "labels", accidentals: "accidentals", clefs: "clef", pitches: "pitch",
                lpversions: "lilypond", pdflinks: "pdf_links", placements: "placement", noteheads: "noteheads",
                voicings: "voicing"};
  Object.entries(segs).forEach(([box, k]) => document.querySelectorAll("#" + box + " input")
    .forEach(r => { r.checked = r.value === draft[k]; }));
  $("placehint").textContent = draft.placement === "nearest"
    ? "each measure starts in root position; every next chord takes the inversion nearest the one before"
    : "every chord in root position, inversions and slash chords as written";
  $("pickcount").textContent = picked.length + " ticked";
  $("pickall").disabled = locked || picked.length === POOL.length;
  $("picknone").disabled = locked || picked.length === 0;
  renderRange();
  $("settings").disabled = locked;
  $("fullrange").disabled = locked;
  const e = estimate(), s = $("summary");
  if (!e){ s.className = "summary"; s.textContent = !POOL.length ? "Loading chords…" : picked.length ? noPermReason() : "Tick at least one chord."; }
  else {
    s.className = "summary" + (e.bytes > 5e9 ? " big" : "");
    s.textContent = e.total.toLocaleString() + " progressions · about " + e.pages.toLocaleString() +
      " page" + (e.pages > 1 ? "s" : "") + " in " + e.pdfs.toLocaleString() + " PDF" + (e.pdfs > 1 ? "s" : "") +
      " · about " + fmtBytes(e.bytes) +
      " · " + e.files.toLocaleString() + " file" + (e.files > 1 ? "s" : "") +
      (draft.write_txt ? " · text about " + fmtBytes(e.txt) + " in " + e.txtFiles.toLocaleString() +
                         " file" + (e.txtFiles > 1 ? "s" : "") : "") +
      (e.bytes > 5e9 ? " — very large: this could take days and fill your disk." : "");
  }
  renderDisk(e);
  renderSummaries(e);
  $("lock").textContent = locked
    ? (status === "stopped" ? "Settings belong to the saved run. Press Reset to change them."
                            : "Settings are locked while a run is in progress.")
    : "";
}

// one-line summaries on the folded sections, and the run bar at the bottom
function renderSummaries(e){
  const o = OPT, d = draft;
  const nh = {filled: "", hollow: "hollow heads", whole: "whole-note heads"}[d.noteheads] || "";
  $("scoresum").textContent = [o.labels[d.labels] + " labels", d.accidentals === "key" ? "key signature" : "accidentals on every note",
    o.voicings[d.voicing].toLowerCase() + " voicing" + (d.double_bass ? " + bass below" : ""),
    o.placements[d.placement].toLowerCase(), nh, o.clefs[d.clef].split(" ")[0] + " clef " + d.pitch,
    "staff " + d.staff_size, d.chunk_labels ? "" : "no chunk labels"].filter(Boolean).join(" · ");
  $("pagessum").textContent = [d.first_page_systems + " / " + d.systems_per_page + " systems",
    d.pages_per_pdf.toLocaleString() + " pages per PDF", d.max_kb.toLocaleString() + " KB files",
    d.save_mode === "custom" && d.save_path.trim() ? "save to " + d.save_path.trim() : $("defaultplace").textContent.toLowerCase(),
    d.write_txt ? "text lists" : "", d.pdf_links !== "off" ? o.pdf_links[d.pdf_links].toLowerCase() : ""].filter(Boolean).join(" · ");
  $("addsum").textContent = d.custom.length ? d.custom.length + " added" : "";
  const extras = d.extras.map(x => o.extras[x][0].toLowerCase());
  $("chordssum").textContent = [KEYLABEL, o.sizes[d.size].toLowerCase().replace("7ths", "7ths").replace("triads", "triads"),
    picked.length + " of " + POOL.length + " chords ticked", extras.length ? "+ " + extras.join(", ") : ""].filter(Boolean).join(" · ");
  const fr = k => { const c = byId(d[k] === true ? TONIC : d[k]); return c ? c.roman : ""; };
  $("progsum").textContent = [d.length + " chords each", RM() === "norepeat" ? "no chord twice in a row" : RM() === "once" ? "each chord once" : "",
    fr("frame_start") ? "start on " + fr("frame_start") : "", fr("frame_end") ? "end on " + fr("frame_end") : "",
    $("rangeinfo").textContent].filter(Boolean).join(" · ");
  $("advsum").textContent = ["LilyPond " + o.lilypond_versions[d.lilypond], d.music_font.trim() || "Emmentaler",
    d.text_font.trim(), (d.outline_fonts || outlineRequired()) ? "music to outline" : ""].filter(Boolean).join(" · ");
  $("rangesum").textContent = $("rangeinfo").textContent;
  renderDock(e);
}
function renderDock(e){
  const busy = status === "running" || status === "paused";
  $("docksum").textContent = busy ? $("pct").textContent + " · " + $("count").textContent
    : e ? e.total.toLocaleString() + " progressions · about " + e.pages.toLocaleString() + " pages · " + fmtBytes(e.bytes)
    : $("summary").textContent;
  $("dockstart").textContent = $("start").textContent;
  $("dockstart").disabled = $("start").disabled;
  $("dockpreview").disabled = $("preview").disabled;
}
$("dockstart").onclick = () => $("start").click();
$("dockpreview").onclick = () => $("preview").click();
$("double_bass").onchange = e => { draft.double_bass = e.target.checked; renderSettings(); };
$("chunk_labels").onchange = e => { draft.chunk_labels = e.target.checked; renderSettings(); };
// remember which sections are open (this browser only)
document.querySelectorAll("details.acc, details.sub").forEach(dt => {
  try { const v = localStorage.getItem("open:" + dt.id); if (v !== null) dt.open = v === "1"; } catch(err){}
  dt.addEventListener("toggle", () => { try { localStorage.setItem("open:" + dt.id, dt.open ? "1" : "0"); } catch(err){} });
});
$("tonic").onchange = e => { draft.key = e.target.value; renderSettings(); loadPool(); };
$("mode").onchange = e => { draft.mode = e.target.value; renderSettings(); loadPool(); };
$("len").oninput = e => { draft.length = +e.target.value; renderSettings(); };
$("kb").oninput = e => { draft.max_kb = +e.target.value; renderSettings(); };
$("staff").oninput = e => { draft.staff_size = +e.target.value; renderSettings(); };
$("systems").oninput = e => { draft.systems_per_page = +e.target.value; renderSettings(); };
$("firstsys").oninput = e => { draft.first_page_systems = +e.target.value; renderSettings(); };
$("ppdf").oninput = e => {
  const digits = e.target.value.replace(/[^0-9]/g, "");
  if (digits !== e.target.value) e.target.value = digits;     // numbers only
  const v = parseInt(digits, 10);
  if (v > 10000){ e.target.value = "10000"; say("Pages per PDF can be at most 10,000."); }
  if (v >= 1) draft.pages_per_pdf = Math.min(v, 10000);
  renderSettings();
};
$("ppdf").onblur = () => { $("ppdf").value = draft.pages_per_pdf; };   // tidy up (empty, 0, >10,000)
$("textfont").oninput = e => { draft.text_font = e.target.value; renderFontStatus(); };
$("musicfont").oninput = e => { draft.music_font = e.target.value; renderMusicFont(); };
let musicFontsKey = "", OUTLINE_REQUIRED = [];
function outlineRequired(){ return OUTLINE_REQUIRED.includes(draft.music_font.trim().toLowerCase()); }
function renderOutline(){
  const req = outlineRequired(), cb = $("outline");
  cb.checked = req || !!draft.outline_fonts;
  cb.disabled = locked || req;                       // Cadence: on, and can't be unticked
  $("outlinelabel").classList.toggle("forced", req);
  $("outlinereq").hidden = !req;
  $("outlinereq").textContent = req ? "Required for " + draft.music_font.trim() +
    " (GPL font): its font data is never embedded in your PDFs." : "";
}
$("outline").onchange = e => {
  if (outlineRequired()){ e.target.checked = true; return; }   // can't switch it off
  draft.outline_fonts = e.target.checked;
};
function renderMusicFont(){
  renderOutline();
  const list = (LP && LP.music_fonts) || [], el = $("musicfontstat"), name = draft.music_font.trim();
  const key = list.join(",");
  if (key !== musicFontsKey){
    musicFontsKey = key; const dl = $("musicfontlist"); dl.innerHTML = "";
    list.forEach(f => { const o = document.createElement("option"); o.value = f; dl.appendChild(o); });
  }
  el.className = "fontstat";
  if (!name){ el.textContent = list.length ? list.length + " music fonts available in LilyPond: " + list.join(", ") + "."
                                           : "Emmentaler is LilyPond's own music font."; return; }
  if (!LP || LP.error){ el.textContent = ""; return; }
  const hit = list.find(f => f.toLowerCase() === name.toLowerCase());
  if (hit){ el.className = "fontstat ok"; el.textContent = "✓ Installed in LilyPond" + (hit !== name ? " (as “" + hit + "”)" : "") + "."; }
  else { el.className = "fontstat bad"; el.textContent = "⚠ Not in LilyPond's fonts folder: LilyPond will stop with an error."; }
}

function renderFontStatus(){
  const el = $("textfontstat"), name = draft.text_font.trim();
  el.className = "fontstat";
  if (!name){ el.textContent = FONTS ? FONTS.length.toLocaleString() + " fonts found on this computer." : "Checking the fonts on this computer…"; return; }
  if (!FONTS){ el.textContent = "Checking the fonts on this computer…"; return; }
  const hit = FONTS.find(f => f.toLowerCase() === name.toLowerCase());
  if (hit){ el.className = "fontstat ok"; el.textContent = "✓ Installed" + (hit !== name ? " (as “" + hit + "”)" : "") + "."; }
  else { el.className = "fontstat bad"; el.textContent = "⚠ Not found among this computer's fonts — LilyPond would fall back to its default."; }
}
async function loadFonts(){
  try {
    const r = await (await fetch("/fonts")).json();
    FONTS = r.fonts; FONT_SOURCE = r.source;
    const dl = $("fontlist"); dl.innerHTML = "";
    FONTS.forEach(f => { const o = document.createElement("option"); o.value = f; dl.appendChild(o); });
  } catch(e){ FONTS = []; }
  renderFontStatus();
}
document.querySelectorAll("input[name=savemode]").forEach(r => {
  r.onchange = () => { draft.save_mode = r.value; renderSettings();
                       if (r.value === "custom" && !draft.save_path) $("savepath").focus(); };
});
$("savepath").oninput = e => { draft.save_path = e.target.value; };
$("wtxt").onchange = e => { draft.write_txt = e.target.checked; renderSettings(); };
$("browse").onclick = async () => {
  $("browse").disabled = true; say("A folder picker is open on your computer…");
  try {
    const r = await (await fetch("/browse", {method: "POST"})).json();
    if (r.error) say(r.error);
    else { if (r.path) draft.save_path = r.path; noteUntil = 0; }
  } finally { renderSettings(); }
};

function render(d){
  status = d.status;
  if (!OPT){
    OPT = d;
    WINDOWED = !!d.windowed;
    if (d.window_note){ $("winnote").textContent = d.window_note; $("winnote").hidden = false; }
    if (WINDOWED) $("preview").title = "Engrave the first page with the current settings and open it in your PDF viewer";
    $("scriptdir").textContent = d.script_dir;
    if (d.default_place) $("defaultplace").textContent = d.default_place;
    fillSelect("tonic", Object.entries(d.tonics));
    fillSelect("mode", Object.entries(d.modes));
    fillSelect("addroot", Object.entries(d.tonics));
    fillSelect("addquality", Object.entries(d.qualities));
    fillSelect("addbass", [["", "no slash"]].concat(Object.entries(d.tonics)));
    buildSeg("sizes", "size", Object.entries(d.sizes), () => loadPool());
    buildExtras();
    buildSeg("labels", "labels", Object.entries(d.labels));
    buildSeg("accidentals", "accidentals", Object.entries(d.accidentals));
    buildSeg("clefs", "clef", Object.entries(d.clefs));
    buildSeg("pitches", "pitch", d.pitches.map(p => [p, p]));
    buildSeg("lpversions", "lilypond", Object.entries(d.lilypond_versions));
    buildSeg("pdflinks", "pdf_links", Object.entries(d.pdf_links));
    buildSeg("placements", "placement", Object.entries(d.placements));
    buildSeg("noteheads", "noteheads", Object.entries(d.noteheads));
    buildSeg("voicings", "voicing", Object.entries(d.voicings));
    document.querySelectorAll("#pitches span").forEach(s => { s.className = "mono"; });
    $("len").min = d.limits.min_len; $("len").max = d.limits.max_len;
    $("kb").min = d.limits.min_kb; $("kb").max = d.limits.max_kb;
    $("staff").min = d.limits.min_staff; $("staff").max = d.limits.max_staff;
    $("systems").min = $("firstsys").min = d.limits.min_systems;
    $("systems").max = $("firstsys").max = d.limits.max_systems;
    $("musicwarn").textContent = d.music_font_warning;
    $("outlinewarn").textContent = d.outline_warning;
    OUTLINE_REQUIRED = d.outline_required || [];
    loadFonts(); loadPresets();
  }
  const wasLocked = locked; locked = d.locked;
  if (!draft || locked || wasLocked){
    const s = d.settings;
    draft = {length: s.length, max_kb: s.max_kb,
             key: s.key || "c", mode: s.mode || "major", size: s.size || "triads",
             extras: (s.extras || []).slice(), custom: JSON.parse(JSON.stringify(s.custom || [])),
             labels: s.labels || "both", accidentals: s.accidentals || "key",
             frame_start: s.frame_start === true ? true : (s.frame_start || ""),
             frame_end: s.frame_end === true ? true : (s.frame_end || ""),
             voicing: s.voicing || "close", double_bass: !!s.double_bass,
             chunk_labels: s.chunk_labels !== false,
             staff_size: s.staff_size || 20,
             systems_per_page: s.systems_per_page || 8,
             first_page_systems: s.first_page_systems || 6,
             pages_per_pdf: s.pages_per_pdf || 100,
             text_font: s.text_font || "", music_font: s.music_font || "",
             save_mode: s.save_to ? "custom" : "default",
             write_txt: !!s.write_txt,
             rstart: s.range_start ? s.range_start.slice() : null,
             rend: s.range_end ? s.range_end.slice() : null,
             save_path: s.save_to || (draft ? draft.save_path : ""),
             clef: s.clef, pitch: s.pitch,
             placement: s.placement || "fixed", noteheads: s.noteheads || "filled",
             lilypond: s.lilypond || "2.26",
             repeat_mode: s.repeat_mode || "all",
             pdf_links: s.pdf_links || "off",
             outline_fonts: !!s.outline_fonts};
    picked = (s.chords || []).slice();
    if (poolFor !== poolKey()) pendingPick = picked.slice();
  }
  loadPool();
  renderSettings();
  renderLilypond(d);
  renderMusicFont();
  renderEngrave(d);

  $("pill").textContent = d.status; $("pill").className = "pill " + d.status;
  $("fill").style.width = d.percent + "%";
  $("pct").textContent = d.percent.toFixed(1) + "%";
  const est = estimate();
  const total = (d.status === "idle" && est) ? est.total.toLocaleString() : d.total_text;  // preview before Start
  $("count").textContent = d.done_text + " / " + total;
  $("elapsed").textContent = fmtTime(d.elapsed);
  $("chunk").textContent = d.chunk;
  $("nfiles").textContent = d.file_total;
  $("msg").textContent = Date.now() < noteUntil ? note : d.message;
  $("recent").textContent = d.recent.join("\n");
  $("outdir").textContent = "· " + d.out_dir;
  // the list is rebuilt only when it changes, keeping its scroll position
  const filesKey = JSON.stringify([d.files, d.current_file]);
  if (filesKey !== lastFilesKey){
    lastFilesKey = filesKey;
    const f = $("files");
    if (!d.files.length && !d.current_file) f.innerHTML = '<span class="empty">None yet.</span>';
    else {
      let ul = f.querySelector("ul");
      const top = ul ? ul.scrollTop : 0;
      const atEnd = ul ? ul.scrollTop + ul.clientHeight >= ul.scrollHeight - 4 : false;
      if (!ul){ f.innerHTML = ""; ul = document.createElement("ul"); f.appendChild(ul); }
      const items = d.files.slice();
      if (d.current_file) items.push(d.current_file + "  (writing)");
      ul.replaceChildren(...items.map(n => { const li = document.createElement("li"); li.textContent = n; return li; }));
      ul.scrollTop = atEnd ? ul.scrollHeight : top;   // following the end? keep following it
    }
  }
  const s = d.status;
  $("start").textContent = (s === "paused" || s === "stopped") ? "Resume"
                         : (s === "done" ? "Start new run" : "Start");
  $("start").disabled = (s === "running") || (!locked && (rangeBad || !estimate()));
  $("pause").disabled = (s !== "running");
  $("stop").disabled = !(s === "running" || s === "paused");
  $("reset").disabled = (s === "running" || s === "paused");
  renderDock(estimate());
}

let lastFilesKey = "";
async function poll(){
  try { render(await (await fetch("/status")).json()); }
  catch(e){ $("msg").textContent = "Lost contact with the program. Is it still running?"; }
}
async function send(action, body){
  noteUntil = 0;   // a new action replaces any earlier warning
  const r = await fetch("/" + action, JSONPOST(body || {}));
  render(await r.json());
}
$("start").onclick = () => {
  if (status === "paused" || status === "stopped") return send("start");
  const e = estimate();
  if (!e){ say(picked.length ? noPermReason() : "Tick at least one chord."); return; }
  const tf = draft.text_font.trim();
  if (tf && FONTS && FONTS.length && !FONTS.some(f => f.toLowerCase() === tf.toLowerCase()) &&
      !confirm("“" + tf + "” wasn't found among this computer's fonts. Use it anyway?")) return;
  // ask only when the music font isn't one LilyPond reports as installed
  const mf = draft.music_font.trim(), mfList = (LP && LP.music_fonts) || [];
  if (mf && !mfList.some(f => f.toLowerCase() === mf.toLowerCase()) &&
      !confirm("Music font “" + mf + "” wasn't found in LilyPond's fonts folder, so LilyPond will probably " +
               "stop with an error. " + $("musicwarn").textContent + " Start anyway?")) return;
  if (rangeBad){ say($("rangewarn").textContent); return; }
  if (!$("diskwarn").hidden && !confirm($("diskwarn").textContent + " Start anyway?")) return;
  if (draft.save_mode === "custom" && !draft.save_path.trim()){
    say("Type or browse to a save folder, or choose “" + $("defaultplace").textContent + "”."); return; }
  if (e.bytes > 5e9 && !confirm("This run is about " + fmtBytes(e.bytes) + ". Start anyway?")) return;
  send("start", startBody());
};
function startBody(){
  if (!estimate()){ say(picked.length ? noPermReason() : "Tick at least one chord."); return null; }
  if (rangeBad){ say($("rangewarn").textContent); return null; }
  return settingsBody();
}
function settingsBody(){
  return {length: draft.length, chords: ordered(), key: draft.key, mode: draft.mode, size: draft.size,
          extras: draft.extras, custom: draft.custom, labels: draft.labels, accidentals: draft.accidentals,
          frame_start: draft.frame_start === true ? TONIC : draft.frame_start,
          frame_end: draft.frame_end === true ? TONIC : draft.frame_end,
          voicing: draft.voicing, double_bass: draft.double_bass, chunk_labels: draft.chunk_labels,
          max_kb: draft.max_kb, staff_size: draft.staff_size, systems_per_page: draft.systems_per_page,
          first_page_systems: draft.first_page_systems, pages_per_pdf: draft.pages_per_pdf,
          text_font: draft.text_font.trim(), music_font: draft.music_font.trim(),
          clef: draft.clef, pitch: draft.pitch, placement: draft.placement, noteheads: draft.noteheads, lilypond: draft.lilypond,
          repeat_mode: RM(), pdf_links: draft.pdf_links,
          outline_fonts: !!draft.outline_fonts || outlineRequired(),
          save_to: draft.save_mode === "custom" ? draft.save_path : "",
          write_txt: draft.write_txt,
          range_start: rangeIsFull() ? null : draft.rstart,
          range_end: rangeIsFull() ? null : draft.rend};
}
$("pause").onclick = () => send("pause");
$("stop").onclick = () => send("stop");
$("reset").onclick = () => {
  if (confirm("Forget the saved progress so you can change settings?")) send("reset");
};
poll(); const pollTimer = setInterval(poll, 250);
</script></body></html>
"""
PAGE = PAGE.replace("@@LOGO@@", harmonarium_logo_svg())

engine = None   # created in main()


def pick_folder(result_file):
    """Runs in a second copy of this program: shows the system folder picker and
    writes the chosen path to result_file."""
    import tkinter as tk
    from tkinter import filedialog
    root = tk.Tk()
    root.withdraw()
    try:
        root.attributes("-topmost", True)   # keep the dialog in front of the browser
        root.lift()
        root.focus_force()
    except Exception:
        pass
    path = filedialog.askdirectory(title="Choose where to save the scores", parent=root) or ""
    with open(result_file, "w", encoding="utf-8") as f:
        f.write(path)


# ---------------- installed fonts ----------------
_font_cache = None
_font_lock = threading.Lock()


def _font_dirs():
    home = os.path.expanduser("~")
    if sys.platform.startswith("win"):
        windir = os.environ.get("WINDIR", r"C:\Windows")
        local = os.environ.get("LOCALAPPDATA", os.path.join(home, "AppData", "Local"))
        return [os.path.join(windir, "Fonts"), os.path.join(local, "Microsoft", "Windows", "Fonts")]
    if sys.platform == "darwin":
        return ["/System/Library/Fonts", "/Library/Fonts", os.path.join(home, "Library", "Fonts")]
    return ["/usr/share/fonts", "/usr/local/share/fonts",
            os.path.join(home, ".fonts"), os.path.join(home, ".local", "share", "fonts")]


def _family_names(path):
    """Family names inside a .ttf/.otf/.ttc/.otc file (from its 'name' table)."""
    names = set()
    try:
        with open(path, "rb") as f:
            data = f.read()
    except OSError:
        return names
    offsets = [0]
    if data[:4] == b"ttcf":
        n = struct.unpack(">I", data[8:12])[0]
        offsets = list(struct.unpack(f">{n}I", data[12:12 + 4 * n]))
    for base in offsets:
        try:
            num_tables = struct.unpack(">H", data[base + 4:base + 6])[0]
            for t in range(num_tables):
                rec = base + 12 + 16 * t
                tag = data[rec:rec + 4]
                if tag != b"name":
                    continue
                off = struct.unpack(">I", data[rec + 8:rec + 12])[0]
                _, count, str_off = struct.unpack(">HHH", data[off:off + 6])
                found = {}
                for k in range(count):
                    r = off + 6 + 12 * k
                    pid, eid, lid, nid, ln, so = struct.unpack(">HHHHHH", data[r:r + 12])
                    if nid not in (1, 16):
                        continue
                    raw = data[off + str_off + so: off + str_off + so + ln]
                    if pid == 3 or pid == 0:
                        txt = raw.decode("utf-16-be", "ignore")
                        english = pid == 0 or lid == 0x409
                    elif pid == 1:
                        txt = raw.decode("mac_roman", "ignore")
                        english = lid == 0
                    else:
                        continue
                    if txt and (english or nid not in found):
                        found[nid] = txt.strip()
                # the typographic family (16) when present, else the family (1)
                fam = found.get(16) or found.get(1)
                if fam:
                    names.add(fam)
        except (struct.error, IndexError):
            continue
    return names


def _fonts_from_lilypond():
    lp = find_lilypond().get("path") or shutil.which("lilypond")   # bundled LilyPond first
    if not lp:
        return set()
    try:
        r = subprocess.run([lp, "-dshow-available-fonts"], capture_output=True,
                           text=True, errors="replace", timeout=120, creationflags=NO_WINDOW)
    except Exception:
        return set()
    fams = set()
    for line in (r.stdout + "\n" + r.stderr).splitlines():
        # "family Name" (2.24+) or "family 12: Name" (older versions)
        m = re.match(r"\s*family\s+(?:\d+\s*:\s*)?(.+?)\s*$", line)
        if m:
            name = m.group(1)
            # skip LilyPond's music-font sizes (emmentaler-20, profondo-brace, ...)
            if not re.search(r"-(\d+|brace)$", name, re.IGNORECASE):
                fams.add(name)
    return fams


def installed_fonts():
    """Font family names on this computer. Asks LilyPond itself when it is on the
    PATH (its list is exactly what it can use); otherwise reads the font files."""
    global _font_cache
    with _font_lock:
        if _font_cache is None:
            fams, source = _fonts_from_lilypond(), "LilyPond"
            if not fams:
                source = "this computer's font folders"
                for d in _font_dirs():
                    for root, _, files in os.walk(d):
                        for name in files:
                            if name.lower().endswith((".ttf", ".otf", ".ttc", ".otc")):
                                fams |= _family_names(os.path.join(root, name))
            _font_cache = {"fonts": sorted(fams, key=str.lower), "source": source}
        return _font_cache


def disk_free(path):
    """Free bytes on the drive holding path (or its nearest existing parent)."""
    p = os.path.abspath(os.path.expanduser(path or DATA_DIR))
    while not os.path.exists(p) and os.path.dirname(p) != p:
        p = os.path.dirname(p)
    try:
        return {"free": shutil.disk_usage(p).free, "path": p}
    except OSError as e:
        return {"error": str(e)}


# ---------------- LilyPond: finding it, previewing, engraving ----------------
CONFIG_FILE = os.path.join(DATA_DIR, "chord_config.json")   # app settings (e.g. LilyPond path)


def load_config():
    try:
        with open(CONFIG_FILE) as f:
            data = json.load(f)
        return data if isinstance(data, dict) else {}
    except (OSError, ValueError):
        return {}


def save_config(cfg):
    tmp = CONFIG_FILE + ".tmp"
    with open(tmp, "w") as f:
        json.dump(cfg, f, indent=2)
    replace_file(tmp, CONFIG_FILE)


NO_WINDOW = 0x08000000 if os.name == "nt" else 0   # Windows: no console window pops up


def lilypond_candidates():
    """(where it came from, path) for every place LilyPond might be, best first."""
    exe = "lilypond.exe" if os.name == "nt" else "lilypond"
    cands = []
    own = load_config().get("lilypond_path")
    if own:
        cands.append(("your setting", own))
    for base in dict.fromkeys((BUNDLE_RESOURCES, RESOURCE_DIR, SCRIPT_DIR)):   # bundled with the app
        for pat in ("lilypond/bin", "lilypond/*/bin", "lilypond-*/bin"):
            for d in sorted(glob.glob(os.path.join(base, pat)), reverse=True):
                cands.append(("bundled", os.path.join(d, exe)))
    found = shutil.which("lilypond")
    if found:
        cands.append(("installed", found))
    home = os.path.expanduser("~")
    if os.name == "nt":
        pats = [os.path.join(os.environ.get(v, ""), "lilypond-*", "bin", exe)
                for v in ("ProgramFiles", "ProgramFiles(x86)", "LOCALAPPDATA") if os.environ.get(v)]
        pats.append(os.path.join(home, "lilypond-*", "bin", exe))
    else:
        pats = [os.path.join(home, "lilypond-*", "bin", exe), "/Applications/lilypond-*/bin/lilypond",
                "/Applications/LilyPond*.app/Contents/Resources/bin/lilypond",
                "/opt/homebrew/bin/lilypond", "/usr/local/bin/lilypond", "/usr/bin/lilypond"]
    for pat in pats:
        for p in sorted(glob.glob(pat), reverse=True):
            cands.append(("installed", p))
    return cands


_lp_lock = threading.Lock()
_lp_info = None


def clear_quarantine(folder):
    """macOS marks files that came in a download (the app's zip) as quarantined, and then
    won't run the programs inside the bundled LilyPond. Clear the mark on that folder
    (only on a Mac; quietly skipped if the folder can't be changed)."""
    if sys.platform != "darwin":
        return
    try:
        subprocess.run(["xattr", "-dr", "com.apple.quarantine", folder],
                       capture_output=True, timeout=60)
    except Exception:
        pass


def find_lilypond(refresh=False):
    """{'path', 'version', 'source'} for the first working LilyPond, or {'error'}."""
    global _lp_info
    with _lp_lock:
        if _lp_info is not None and not refresh:
            return _lp_info
        info, tried = None, []
        for source, path in lilypond_candidates():
            if not os.path.isfile(path):
                if source == "your setting":
                    tried.append(f"{path} (not found)")
                continue
            if source == "bundled":
                clear_quarantine(lilypond_root(path))
            try:
                r = subprocess.run([path, "--version"], capture_output=True, text=True,
                                   timeout=60, creationflags=NO_WINDOW)
                m = re.search(r"GNU LilyPond (\d+\.\d+\.\d+)", r.stdout + r.stderr)
            except Exception as e:
                tried.append(f"{path} ({e})")
                continue
            if m:
                info = {"path": os.path.abspath(path), "version": m.group(1), "source": source,
                        "music_fonts": lilypond_music_fonts(path)}
                break
            tried.append(f"{path} (didn't report a LilyPond version)")
        _lp_info = info or {"error": "LilyPond wasn't found." + (" Tried: " + "; ".join(tried) if tried else "")}
        return _lp_info


MUSIC_FONT_SIZES = (11, 13, 14, 16, 18, 20, 23, 26)


def lilypond_music_fonts(path):
    """Music fonts installed in this LilyPond (complete sets of -11 ... -26 .otf files)."""
    names = set()
    for d in glob.glob(os.path.join(lilypond_root(path), "share", "lilypond", "*", "fonts", "otf")):
        for f in os.listdir(d):
            m = re.match(r"^(.+)-20\.otf$", f)
            if m and m.group(1) != "emmentaler" and all(
                    os.path.exists(os.path.join(d, f"{m.group(1)}-{z}.otf")) for z in MUSIC_FONT_SIZES):
                names.add(m.group(1))
    return sorted(names)


def lilypond_root(path):
    """.../lilypond-2.26.0/bin/lilypond -> .../lilypond-2.26.0"""
    return os.path.dirname(os.path.dirname(os.path.realpath(path)))


PREVIEW_DIR = os.path.join(tempfile.gettempdir(), "harmonarium-preview")
_preview_lock = threading.Lock()


def make_preview(raw):
    """Engrave the first page of the current settings into PREVIEW_DIR/preview.pdf."""
    settings, err = validate(raw)
    if err:
        return {"ok": False, "error": err}
    lp = find_lilypond()
    if not lp.get("path"):
        return {"ok": False, "error": lp.get("error", "LilyPond wasn't found.")}
    plan = Plan(settings)
    with _preview_lock:
        shutil.rmtree(PREVIEW_DIR, ignore_errors=True)
        os.makedirs(PREVIEW_DIR, exist_ok=True)
        with open(os.path.join(PREVIEW_DIR, CC0_EPS_NAME), "w") as f:
            f.write(CC0_EPS)
        last = min(plan.last, plan.first + plan.first_page_measures - 1)
        with open(os.path.join(PREVIEW_DIR, "preview.ly"), "w") as f:
            f.write(plan.whole_file(plan.first, last, 1, "preview"))
        try:
            r = subprocess.run([lp["path"], "preview.ly"], cwd=PREVIEW_DIR, capture_output=True,
                               text=True, errors="replace", timeout=300, creationflags=NO_WINDOW)
            log = r.stdout + r.stderr
        except subprocess.TimeoutExpired:
            return {"ok": False, "error": "LilyPond took too long (over 5 minutes)."}
        notes = [l.strip() for l in log.splitlines() if re.search(r"(warning|error):", l)]
        ok = r.returncode == 0 and os.path.exists(os.path.join(PREVIEW_DIR, "preview.pdf"))
        if ok and plan.outline_fonts and music_font_embedded(os.path.join(PREVIEW_DIR, "preview.pdf"),
                                                             plan.music_font):
            notes.insert(0, "Output to outline didn't take effect: the music font is embedded in this PDF.")
        return {"ok": ok, "warnings": notes[:20],
                "error": None if ok else "LilyPond reported a problem:\n" + "\n".join(log.splitlines()[-15:])}


def lilypond_crashed(code):
    """True if LilyPond crashed rather than stopping with an error of its own: a Windows
    exception code such as 0xC0000005 (access violation), or a signal on Mac/Linux."""
    return code is not None and (code < 0 or code >= 0xC0000000)


def crash_code_text(code):
    if code is not None and code >= 0xC0000000:
        name = {0xC0000005: "access violation", 0xC00000FD: "stack overflow",
                0xC0000017: "out of memory", 0xC0000409: "stack buffer overrun"}.get(code)
        return f"Windows error 0x{code:08X}" + (f", {name}" if name else "")
    if code is not None and code < 0:
        return f"signal {-code}"
    return f"exit code {code}"


def explain_lilypond_failure(log, code):
    """Plain-English reasons for a failed engraving, from LilyPond's output."""
    reasons, seen = [], set()

    def add(text):
        if text not in seen:
            seen.add(text)
            reasons.append(text)
    for line in log.splitlines():
        m = re.search(r"cannot rename .* to [`'\"]?([^`'\"]+\.pdf)", line)
        if m:
            add(f"Couldn't save {m.group(1)}: it is probably open in a PDF viewer or browser "
                "(Windows can't replace an open file). Close it and press Engrave PDFs again.")
            continue
        if re.search(r"bad_alloc|out of memory|memory exhausted|cannot allocate", line, re.I):
            add("LilyPond ran out of memory. Lower \"Pages per PDF\" (or the file size) and run again.")
            continue
        m = re.search(r"cannot find font [`'\"]?([^`'\" ]+)", line)
        if m:
            add(f"The music font {m.group(1)} isn't installed in LilyPond's fonts folder.")
            continue
        if re.search(r"cannot (open|write)|Permission denied|No space left", line, re.I):
            add("LilyPond couldn't write to the folder (no permission, or the disk is full): " + line.strip())
            continue
        if "Output to outline didn't take effect" in line:
            add(line.strip())
            continue
        if re.search(r"\b(fatal error|error|programming error):", line):
            add("LilyPond reported: " + line.strip())
    if not reasons and lilypond_crashed(code):
        add(f"LilyPond crashed ({crash_code_text(code)}). The app engraved each PDF in this file "
            "on its own, twice, and it still crashed. Try a lower \"Pages per PDF\" or file size "
            "and run again; the PDFs that were made are kept.")
    if not reasons:
        if not log.strip():
            add(f"LilyPond stopped without any message (exit code {code}). It may have been closed by "
                "antivirus software or run out of memory.")
        else:
            add(f"LilyPond stopped with exit code {code} without naming an error; see the full log.")
    return reasons


class Engraver:
    """Engraves a run's score files one at a time (one LilyPond process each)."""

    def __init__(self):
        self.lock = threading.Lock()
        self.proc = None
        self.stop_flag = False
        self.status = "idle"            # idle | running | done | stopped
        self.folder = ""
        self.current = ""
        self.done = self.total = self.skipped = 0
        self.failed = []                # [{"file", "log"}]
        self.started = 0.0

    @staticmethod
    def up_to_date(path):
        """True if every PDF this score file makes exists and is newer than the file."""
        try:
            with open(path, encoding="ascii", errors="replace") as f:
                names = re.findall(r'\\bookOutputName "([^"]+)"', f.read())
            mtime = os.path.getmtime(path)
        except OSError:
            return False
        folder = os.path.dirname(path)
        return bool(names) and all(
            os.path.exists(os.path.join(folder, n + ".pdf"))
            and os.path.getmtime(os.path.join(folder, n + ".pdf")) >= mtime for n in names)

    @staticmethod
    def outline_failures(path):
        """For a score file set to output music to outline: PDFs that still embed the music font (deleted)."""
        try:
            with open(path, encoding="utf-8", errors="replace") as f:
                text = f.read()
        except OSError:
            return []
        mark = re.search(OUTLINE_MARK_RE, text)
        if not mark:
            return []
        bad = []
        for n in re.findall(r'\\bookOutputName "([^"]+)"', text):
            pdf = os.path.join(os.path.dirname(path), n + ".pdf")
            if music_font_embedded(pdf, mark.group(1)):
                bad.append(n + ".pdf")
                try:
                    os.remove(pdf)
                except OSError:
                    pass
        return bad

    def start(self, folder, files, lilypond):
        with self.lock:
            if self.status == "running":
                return
            self.status, self.folder, self.stop_flag = "running", folder, False
            self.current, self.done, self.total, self.skipped = "", 0, len(files), 0
            self.failed, self.started = [], time.time()
        threading.Thread(target=self._run, args=(folder, list(files), lilypond), daemon=True).start()

    def stop(self):
        with self.lock:
            self.stop_flag = True
            if self.proc and self.proc.poll() is None:
                self.proc.terminate()

    def _run(self, folder, files, lilypond):
        for name in files:
            if self.stop_flag:
                break
            path = os.path.join(folder, name)
            if self.up_to_date(path):
                with self.lock:
                    self.done += 1
                    self.skipped += 1
                continue
            with self.lock:
                self.current = name
                try:
                    self.proc = subprocess.Popen([lilypond, name], cwd=folder, stdout=subprocess.PIPE,
                                                 stderr=subprocess.STDOUT, text=True, errors="replace",
                                                 creationflags=NO_WINDOW)
                except OSError as e:
                    self.failed.append({"file": name, "reasons": [f"LilyPond couldn't be started: {e}"],
                                        "code": None, "log": "", "logfile": ""})
                    self.done += 1
                    continue
            out = self.proc.communicate()[0]
            if lilypond_crashed(self.proc.returncode) and not self.stop_flag:
                first = self.proc
                out, code = self._retry_by_book(folder, name, lilypond, out, first.returncode)
                with self.lock:
                    self.proc = first
                first.returncode = code
            if self.proc.returncode == 0 and not self.stop_flag:
                bad = self.outline_failures(path)
                if bad:
                    out += ("\nOutput to outline didn't take effect: the music font is embedded in "
                            + ", ".join(bad) + ". These PDFs were deleted.")
                    self.proc.returncode = 1
            with self.lock:
                if self.proc.returncode != 0 and not self.stop_flag:
                    # keep LilyPond's whole output next to the score file for reference
                    logfile = os.path.splitext(name)[0] + ".log"
                    try:
                        with open(os.path.join(folder, logfile), "w", encoding="utf-8") as f:
                            f.write(out)
                    except OSError:
                        logfile = ""
                    lines = [l for l in out.splitlines() if not re.match(r"^(Interpreting music|Preprocessing|"
                             r"Calculating|Drawing|Fitting|Finding|Processing|Parsing|Converting|Layout)", l)]
                    self.failed.append({"file": name, "code": self.proc.returncode, "logfile": logfile,
                                        "reasons": explain_lilypond_failure(out, self.proc.returncode),
                                        "log": "\n".join(lines[-6:])})
                if not self.stop_flag:
                    self.done += 1
                self.proc = None
        with self.lock:
            self.status = "stopped" if self.stop_flag else "done"
            self.current = ""

    def _retry_by_book(self, folder, name, lilypond, out, code):
        """LilyPond crashed partway through a score file. Engrave each of its PDFs (each
        \\book) again in a LilyPond of its own, trying each one twice; a crash like this is
        often a one-off, and a smaller job also needs much less memory. PDFs the crashed
        run already finished are kept. Returns (log, exit code: 0 if every PDF is made)."""
        path = os.path.join(folder, name)
        try:
            with open(path, encoding="utf-8", errors="replace") as f:
                text = f.read()
            mtime = os.path.getmtime(path)
        except OSError:
            return out, code
        starts = [m.start() for m in re.finditer(r"(?m)^\\book \{", text)]
        if not starts:
            return out, code
        log = [out, f"\n=== LilyPond crashed ({crash_code_text(code)}). "
                    "Engraving each PDF in this file on its own. ===\n"]
        final = 0
        for k, (a, b) in enumerate(zip(starts, starts[1:] + [len(text)])):
            book = text[a:b]
            m = re.search(r'\\bookOutputName "([^"]+)"', book)
            pdf = os.path.join(folder, (m.group(1) if m else "") + ".pdf")
            if m and os.path.exists(pdf) and os.path.getmtime(pdf) >= mtime:
                log.append(f"--- {m.group(1)}.pdf: already made before the crash ---\n")
                continue
            part = f"_retry{k + 1}.ly"
            try:
                with open(os.path.join(folder, part), "w", encoding="utf-8") as f:
                    f.write(text[:starts[0]] + book)
            except OSError as e:
                log.append(f"--- couldn't write {part}: {e} ---\n")
                final = code
                continue
            proc = None
            for attempt in (1, 2):
                if self.stop_flag:
                    break
                label = (m.group(1) + ".pdf") if m else f"PDF {k + 1}"
                log.append(f"--- {label}: attempt {attempt} ---\n")
                with self.lock:
                    try:
                        self.proc = subprocess.Popen([lilypond, part], cwd=folder, stdout=subprocess.PIPE,
                                                     stderr=subprocess.STDOUT, text=True, errors="replace",
                                                     creationflags=NO_WINDOW)
                    except OSError as e:
                        log.append(f"LilyPond couldn't be started: {e}\n")
                        self.proc = None
                        break
                proc = self.proc
                log.append(proc.communicate()[0])
                if proc.returncode == 0 or not lilypond_crashed(proc.returncode):
                    break
                log.append(f"(crashed again: {crash_code_text(proc.returncode)})\n")
            rc = proc.returncode if proc is not None else 1
            if self.stop_flag:
                rc = rc or 1
            if rc != 0:
                final = rc
            try:
                os.remove(os.path.join(folder, part))
            except OSError:
                pass
            if self.stop_flag:
                break
        if final == 0:
            log.append("=== Every PDF in this file was made. ===\n")
        return "".join(log), final

    def snapshot(self):
        with self.lock:
            return {"status": self.status, "done": self.done, "total": self.total,
                    "skipped": self.skipped, "current": self.current, "failed": self.failed[-5:],
                    "failed_count": len(self.failed), "elapsed": time.time() - self.started if self.started else 0}


engraver = Engraver()


# ---------------- acknowledgements ----------------
FRIENDLY = {"tg2_501otf": "TeX Gyre fonts (2.501)", "urw-base35-fonts": "URW base 35 fonts",
            "gc": "Boehm–Demers–Weiser garbage collector", "Python": "Python (used by LilyPond's tools)"}


def app_licenses_dir():
    for base in dict.fromkeys((RESOURCE_DIR, BUNDLE_RESOURCES, SCRIPT_DIR)):
        d = os.path.join(base, "licenses")
        if os.path.isdir(d):
            return d
    return None


def license_dirs():
    """Folders the acknowledgements page may show license files from."""
    dirs = {}
    a = app_licenses_dir()
    if a:
        dirs["app"] = a
    lp = find_lilypond()
    if lp.get("path") and os.path.isdir(os.path.join(lilypond_root(lp["path"]), "licenses")):
        dirs["lilypond"] = os.path.join(lilypond_root(lp["path"]), "licenses")
    return dirs


def read_license(src, rel):
    """Text of one license file, only from the known license folders."""
    base = license_dirs().get(src)
    if not base:
        return None
    path = os.path.realpath(os.path.join(base, rel))
    if not path.startswith(os.path.realpath(base) + os.sep) or not os.path.isfile(path):
        return None
    with open(path, encoding="utf-8", errors="replace") as f:
        return f.read()


def font_license_summary(text):
    """(license name, copyright notice) for a bundled font's license file."""
    if "Open Font License" in text:
        return ("SIL Open Font License, Version 1.1",
                text.split("This Font Software is licensed")[0].strip())
    if "GNU General Public License" in text:
        later = "any later version" in text
        ver = re.search(r"either version (\d)", text) or re.search(r"Version (\d), ", text)
        lic = "GNU General Public License" + (f", version {ver.group(1)}" if ver else "") + (" or later" if later else "")
        notice = " ".join(l.strip() for l in text.split("This program is free software")[0].splitlines()
                          if l.strip())
        return lic, notice
    if "UNRESTRICTED" in text:
        who = re.search(r"I, ([^,]+),\s+hereby\s+disclaim", text)
        return ("Unrestricted use (copyright disclaimed)",
                (f"Font files: {who.group(1)} disclaims all copyright; anyone may use, copy, modify and "
                 "redistribute them with no conditions. " if who else "")
                + ("Source code: MIT license." if "Permission is hereby granted, free of charge" in text else ""))
    return "see license", ""


def acknowledgements_html():
    from html import escape as esc
    dirs, lp = license_dirs(), find_lilypond()
    link = lambda src, rel, label=None: (f'<a href="/license?src={src}&amp;f={esc(rel)}" target="_blank">'
                                         f'{esc(label or os.path.basename(rel))}</a>')
    out = ["<!doctype html><html lang='en'><head><meta charset='utf-8'>",
           "<meta name='viewport' content='width=device-width, initial-scale=1'><title>Acknowledgements</title>"
           "<link rel='icon' href='/logo.svg' type='image/svg+xml'><script>try{var t=localStorage.getItem('harmonarium-theme');if(t==='dark'||t==='light')document.documentElement.dataset.theme=t;}catch(e){}</script><style>",
           ":root{--bg:#f6f5f2;--card:#fff;--ink:#1d1d1f;--muted:#6b6b70;--line:#e3e1dc;--accent:#2f6f5e}",
           "@media (prefers-color-scheme:dark){:root:not([data-theme=light]){--bg:#151517;--card:#1f1f22;--ink:#ececee;--muted:#9a9aa1;--line:#2e2e33;--accent:#5fb39b}}:root[data-theme=dark]{--bg:#151517;--card:#1f1f22;--ink:#ececee;--muted:#9a9aa1;--line:#2e2e33;--accent:#5fb39b}",
           "body{margin:0;background:var(--bg);color:var(--ink);font:15px/1.55 -apple-system,BlinkMacSystemFont,'Segoe UI',Roboto,sans-serif}",
           "main{max-width:760px;margin:0 auto;padding:28px 16px 48px}h1{font-size:24px;margin:0 0 6px}",
           "h2{font-size:15px;text-transform:uppercase;letter-spacing:.05em;color:var(--muted);margin:28px 0 10px}",
           ".item{background:var(--card);border:1px solid var(--line);border-radius:10px;padding:12px 14px;margin-bottom:8px}",
           ".item b{font-size:15px}.small{color:var(--muted);font-size:13px}a{color:var(--accent)}",
           "pre{white-space:pre-wrap;font-size:12px;background:var(--bg);padding:10px;border-radius:6px;max-height:320px;overflow:auto}",
           "</style></head><body><main>",
           "<h1>Acknowledgements</h1>",
           "<p class='small'>Harmonarium is built with, and includes, the free software and fonts below, "
           "used under their licenses. Click a license name to read it in full.</p>"]

    # ---- the app's own license (GPL v3 section 5(d): the "Appropriate Legal Notices") ----
    out.append("<h2 id='license'>Harmonarium</h2><div class='item'><b>GNU General Public License, version 3 "
               "or later</b>"
               f"<div class='small'>{esc(APP_COPYRIGHT)}. Harmonarium is free software: you can redistribute it "
               "and/or modify it under the terms of the GNU General Public License as published by the Free "
               "Software Foundation, either version 3 of the License, or (at your option) any later version. "
               "The Harmonarium logo is licensed under the same terms.</div>"
               "<div class='small'><b>There is no warranty</b>: Harmonarium is distributed in the hope that it "
               "will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or "
               "FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public License for details.</div>"
               "<div class='small'>The GPL covers Harmonarium's own code and logo, not the scores you make "
               "with it (see below). Everything else listed here keeps its own license.</div>"
               "<div class='small'><a href='/license/gpl' target='_blank'>GNU GPL v3 (full text)</a> · "
               f"<a href='{APP_SOURCE_URL}' target='_blank'>Source code</a></div></div>")

    # ---- the scores ----
    out.append("<h2>Your scores</h2><div class='item'><b>CC0 1.0 Universal</b> — the scores carry a "
               "<a href='https://creativecommons.org/publicdomain/zero/1.0/' target='_blank'>CC0 public domain dedication</a> (<a href='/license/cc0' target='_blank'>full legal text</a>). Harmonarium's GPL doesn't apply to them."
               "<div class='small'>The CC0 badge printed on each page is a trademark of Creative Commons, used under the "
               "<a href='https://creativecommons.org/policies' target='_blank'>Creative Commons trademark policy</a> "
               "with a link to the CC0 deed. It comes from Creative Commons' "
               "<a href='https://github.com/creativecommons/vocabulary' target='_blank'>vocabulary</a> design system "
               "(80×15 badge), converted from SVG to EPS without changing the design.</div></div>")

    # ---- music fonts ----
    out.append("<h2>Music fonts</h2>")
    fonts = []
    if dirs.get("app") and os.path.isdir(os.path.join(dirs["app"], "fonts")):
        for name in sorted(os.listdir(os.path.join(dirs["app"], "fonts")), key=str.lower):
            fdir = os.path.join(dirs["app"], "fonts", name)
            files = sorted(f for f in os.listdir(fdir) if os.path.isfile(os.path.join(fdir, f))) if os.path.isdir(fdir) else []
            if files:
                fonts.append((name, files))
    for name, files in fonts:
        includes = read_license("app", f"fonts/{name}/INCLUDES.txt") if "INCLUDES.txt" in files else ""
        files = [f for f in files if f != "INCLUDES.txt"]
        main = next((f for f in files if f.lower().startswith(("ofl", "license", "licence"))), files[0])
        text = read_license("app", f"fonts/{name}/{main}") or ""
        lic, notice = font_license_summary(text)
        if name.lower() in OUTLINE_REQUIRED:
            notice += ("\nUsed only with “output music to outline”: the music symbols are drawn as shapes, "
                       "so no font data from it is embedded in your PDFs.")
        rfn = re.search(r'Reserved Font Names?\s+"?([^"\n.]+)"?', text)
        title = rfn.group(1).strip() if rfn else name.capitalize()
        out.append(f"<div class='item'><b>{esc(title)}</b> <span class='small'>({esc(name)})</span> — {esc(lic)}"
                   + "".join(f"<div class='small'>{esc(line)}</div>" for line in notice.split("\n") if line)
                   + (f"<div class='small'>{esc(includes.strip())}</div>" if includes else "")
                   + "<div class='small'>" + " · ".join(link('app', f'fonts/{name}/{f}', f) for f in files) + "</div></div>")
    out.append("<div class='item'><b>Emmentaler</b> (LilyPond's own music font) — SIL Open Font License, Version 1.1, "
               "or GPL with font exception<div class='small'>Copyright (c) 1996–2026, The LilyPond authors (lilypond.org), "
               "with Reserved Font Names “Emmentaler” and “Feta”.</div>"
               + (f"<div class='small'>{link('app', 'emmentaler/OFL.txt', 'OFL.txt')}</div>"
                  if read_license("app", "emmentaler/OFL.txt") else "") + "</div>")
    if not fonts:
        out.append("<p class='small'>No other music fonts are bundled yet.</p>")
    out.append("<h2>Control panel font</h2><div class='item'><b>Academico</b> (Regular and Bold, version 0.905) — "
               "SIL Open Font License, Version 1.1<div class='small'>Copyright (c) 2017-2025 Steinberg Media "
               "Technologies GmbH (steinberg.net), with Reserved Font Name “Academico”. Bundled unmodified and used "
               "for chord names and numerals in this control panel (not in your scores).</div>"
               "<div class='small'><a href='/license/academico' target='_blank'>Full license (COPYING)</a> · "
               "<a href='https://github.com/dbenjaminmiller/academico-mirror' target='_blank'>source</a></div></div>")
    out.append("<p class='small'>Text fonts are not bundled: any text font you choose comes from your own "
               "computer and is used under its own license.</p>")

    # ---- LilyPond and what it includes ----
    out.append("<h2>LilyPond</h2>")
    if lp.get("path"):
        v = lp["version"]
        out.append(f"<div class='item'><b>GNU LilyPond {esc(v)}</b> — GNU General Public License, version 3 or later"
                   f"<div class='small'>Engraves the scores. Source code: "
                   f"<a href='https://lilypond.org/download/sources/v{'.'.join(v.split('.')[:2])}/lilypond-{v}.tar.gz' target='_blank'>"
                   f"lilypond-{v}.tar.gz</a> from <a href='https://lilypond.org' target='_blank'>lilypond.org</a>.</div></div>")
        if dirs.get("lilypond"):
            groups = {}
            for f in sorted(os.listdir(dirs["lilypond"]), key=str.lower):
                m = re.match(r"^(.*?)\.(?=[A-Z])", f)
                groups.setdefault(m.group(1) if m else f, []).append(f)
            out.append("<p class='small'>LilyPond's package includes these components, each under its own license "
                       "(their source code is available from each project):</p>")
            for comp, files in groups.items():
                m = re.match(r"^(.*?)-(\d[\w.]*)$", comp)
                name, ver = (m.group(1), m.group(2)) if m else (comp, "")
                label = FRIENDLY.get(name, FRIENDLY.get(comp, name))
                out.append(f"<div class='item'><b>{esc(label)}</b> {esc(ver)}<div class='small'>"
                           + " · ".join(link('lilypond', f) for f in files) + "</div></div>")
    else:
        out.append("<p class='small'>LilyPond wasn't found, so its components can't be listed here.</p>")

    # ---- the app itself: Python and the packages packed in with it ----
    out.append("<h2>This app</h2><div class='item'><b>Python</b> — Python Software Foundation License"
               "<div class='small'>The packaged app includes the Python runtime and its standard library "
               "(including Tcl/Tk for the folder picker). <a href='https://docs.python.org/3/license.html' target='_blank'>"
               "Python license</a> · <a href='https://www.tcl.tk/software/tcltk/license.html' target='_blank'>Tcl/Tk license</a></div></div>"
               "<div class='item'><b>PyInstaller</b> — GPL version 2 or later, with a bootloader exception"
               "<div class='small'>Packages the app. The small starter program it adds is covered by that "
               "exception, so it doesn't change Harmonarium's own license. "
               "<a href='https://pyinstaller.org/en/stable/license.html' target='_blank'>PyInstaller license</a></div></div>")
    pkgs, extras, bundled = bundled_packages()
    if pkgs:
        out.append("<p class='small'>" + ("Packed into this app for its window:" if bundled else
                   "Used for the app window, from this computer's Python (not part of Harmonarium):") + "</p>")
    for p in pkgs:
        files = " · ".join(link("app", f, os.path.basename(f)) for f in p.get("files", []))
        home = (f"<a href='{esc(p['home'])}' target='_blank'>project page</a>" if p.get("home") else "")
        out.append(f"<div class='item'><b>{esc(p['name'])}</b> {esc(p.get('version', ''))} — {esc(p.get('license', ''))}"
                   + (f"<div class='small'>{esc(p['summary'])}</div>" if p.get("summary") else "")
                   + (f"<div class='small'>{' · '.join(x for x in (files, home) if x)}</div>" if files or home else "")
                   + "</div>")
    for x in extras:
        files = " · ".join(link("app", f, os.path.basename(f)) for f in x.get("files", []))
        url = (f"<a href='{esc(x['url'])}' target='_blank'>license</a>" if x.get("url") else "")
        out.append(f"<div class='item'><b>{esc(x['name'])}</b> — {esc(x.get('license', ''))}"
                   + (f"<div class='small'>{esc(x['note'])}</div>" if x.get("note") else "")
                   + (f"<div class='small'>{' · '.join(v for v in (files, url) if v)}</div>" if files or url else "")
                   + "</div>")
    out.append("</main></body></html>")
    return "\n".join(out)


PRESETS_FILE = os.path.join(DATA_DIR, "chord_presets.json")


def load_presets():
    try:
        with open(PRESETS_FILE) as f:
            data = json.load(f)
        return data if isinstance(data, dict) else {}
    except (OSError, ValueError):
        return {}


def save_presets(presets):
    tmp = PRESETS_FILE + ".tmp"
    with open(tmp, "w") as f:
        json.dump(presets, f, indent=2)
    replace_file(tmp, PRESETS_FILE)


MAC_PICKER = [
    "activate",   # bring the dialog to the front, above the browser
    'set chosen to choose folder with prompt "Choose where to save the scores"',
    "return POSIX path of chosen",
]


def browse_for_folder():
    """Show the computer's own folder picker (the app window's own, when it's open).
    Mac: the system "choose folder" dialog via AppleScript (brought to the front).
    Windows (and others): the standard folder dialog via Tk, shown by a short-lived
    second copy of this program so it is safe whether packaged or not."""
    native = native_folder_dialog()
    if native is not None:
        return native
    if sys.platform == "darwin":
        cmd = ["osascript"]
        for line in MAC_PICKER:
            cmd += ["-e", line]
        try:
            r = subprocess.run(cmd, capture_output=True, text=True, timeout=600)
        except Exception:
            return {"error": "Couldn't open the folder picker. Type the path instead."}
        if r.returncode != 0:
            if "-128" in r.stderr:          # the user pressed Cancel
                return {"path": ""}
            return {"error": "Couldn't open the folder picker. Type the path instead."}
        path = r.stdout.strip()
        return {"path": path.rstrip("/") or "/"}

    import tempfile
    fd, result_file = tempfile.mkstemp(suffix=".txt")
    os.close(fd)
    if getattr(sys, "frozen", False):
        cmd = [sys.executable, "--pick-folder", result_file]
    else:
        cmd = [sys.executable, os.path.abspath(__file__), "--pick-folder", result_file]
    try:
        r = subprocess.run(cmd, timeout=600)
        with open(result_file, encoding="utf-8") as f:
            path = f.read().strip()
    except Exception:
        r, path = None, ""
    finally:
        try:
            os.remove(result_file)
        except OSError:
            pass
    if r is None or r.returncode != 0:
        return {"error": "Couldn't open a folder picker on this computer. Type the path instead."}
    return {"path": path}


class Handler(BaseHTTPRequestHandler):
    def _send(self, body, ctype):
        data = body.encode("utf-8")
        self.send_response(200)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(data)))
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        self.wfile.write(data)

    def do_GET(self):
        from urllib.parse import urlparse, parse_qs
        url = urlparse(self.path)
        if url.path == "/ping":               # lets a second launch find this one
            self._send(json.dumps({"app": APP_NAME}), "application/json")
        elif url.path == "/diskfree":
            path = (parse_qs(url.query).get("path") or [""])[0]
            self._send(json.dumps(disk_free(path)), "application/json")
        elif url.path == "/presets":
            self._send(json.dumps(load_presets()), "application/json")
        elif url.path.startswith("/fonts/") and url.path[7:] in PANEL_FONTS:
            data = PANEL_FONTS[url.path[7:]]
            self.send_response(200)
            self.send_header("Content-Type", "font/otf")
            self.send_header("Content-Length", str(len(data)))
            self.send_header("Cache-Control", "max-age=86400")
            self.end_headers()
            self.wfile.write(data)
        elif url.path == "/license/gpl":
            self._send(GPL3_TEXT, "text/plain; charset=utf-8")
        elif url.path == "/license/cc0":
            self._send(CC0_TEXT, "text/plain; charset=utf-8")
        elif url.path == "/license/academico":
            self._send(ACADEMICO_LICENSE, "text/plain; charset=utf-8")
        elif url.path == "/guide":
            self._send(guide_html(), "text/html; charset=utf-8")
        elif url.path == "/guide.md":
            self._send(USER_GUIDE_MD, "text/markdown; charset=utf-8")
        elif url.path == "/logo.svg":
            self._send(LOGO_SVG, "image/svg+xml")
        elif url.path == "/acknowledgements":
            self._send(acknowledgements_html(), "text/html; charset=utf-8")
        elif url.path == "/license":
            q = parse_qs(url.query)
            text = read_license((q.get("src") or [""])[0], (q.get("f") or [""])[0])
            if text is None:
                self.send_error(404)
            else:
                self._send(text, "text/plain; charset=utf-8")
        elif url.path == "/preview.pdf":
            try:
                with open(os.path.join(PREVIEW_DIR, "preview.pdf"), "rb") as f:
                    data = f.read()
            except OSError:
                self.send_error(404)
                return
            self.send_response(200)
            self.send_header("Content-Type", "application/pdf")
            self.send_header("Content-Length", str(len(data)))
            self.send_header("Cache-Control", "no-store")
            self.end_headers()
            self.wfile.write(data)
        elif self.path == "/":
            self._send(PAGE, "text/html; charset=utf-8")
        elif self.path == "/fonts":
            self._send(json.dumps(installed_fonts()), "application/json")
        elif self.path == "/status":
            self._send(json.dumps(engine.snapshot()), "application/json")
        else:
            self.send_error(404)

    def do_POST(self):
        length = int(self.headers.get("Content-Length") or 0)
        try:
            body = json.loads(self.rfile.read(length) or b"{}")
        except ValueError:
            body = {}
        if self.path == "/start":
            engine.start(body)
        elif self.path == "/pause":
            engine.pause()
        elif self.path == "/stop":
            engine.stop()
        elif self.path == "/browse":
            self._send(json.dumps(browse_for_folder()), "application/json")
            return
        elif self.path == "/reset":
            engine.reset()
        elif self.path == "/presets":          # save {"name", "preset"}
            name = str(body.get("name", "")).strip()[:60]
            presets = load_presets()
            if name and isinstance(body.get("preset"), dict):
                presets[name] = body["preset"]
                save_presets(presets)
            self._send(json.dumps(presets), "application/json")
            return
        elif self.path == "/presets/delete":   # {"name"}
            presets = load_presets()
            presets.pop(str(body.get("name", "")), None)
            save_presets(presets)
            self._send(json.dumps(presets), "application/json")
            return
        elif self.path == "/lilypond":          # {"path": ""} = find it automatically
            cfg = load_config()
            cfg["lilypond_path"] = str(body.get("path", "")).strip().strip('"')
            save_config(cfg)
            self._send(json.dumps(find_lilypond(refresh=True)), "application/json")
            return
        elif self.path == "/fit":             # systems that fit on a page, for the panel
            self._send(json.dumps(fit_json(body)), "application/json")
            return
        elif self.path == "/pool":            # the chords to choose from, for the panel
            self._send(json.dumps(pool_json(body)), "application/json")
            return
        elif self.path == "/guide/open":       # app window: the guide in its own window
            self._send(json.dumps(open_guide_window(str(body.get("anchor", "")))), "application/json")
            return
        elif self.path == "/preview/open":     # app window: show the preview in the PDF app
            self._send(json.dumps(open_preview_in_viewer()), "application/json")
            return
        elif self.path == "/preview":
            self._send(json.dumps(make_preview(body)), "application/json")
            return
        elif self.path == "/engrave":
            lp = find_lilypond()
            snap = engine.snapshot()
            if lp.get("path") and snap["status"] != "running":
                engraver.start(engine.plan.out_dir, list(engine.state.get("files", [])), lp["path"])
        elif self.path == "/engrave/stop":
            engraver.stop()
        elif self.path == "/quit":
            engraver.stop()
            engine.stop()                      # saves progress
            self._send(json.dumps({"ok": True}), "application/json")
            if WINDOW is not None:            # the app window: closing it ends the program
                threading.Timer(0.4, WINDOW.destroy).start()
            else:
                threading.Thread(target=SERVER.shutdown, daemon=True).start()
            return
        else:
            self.send_error(404)
            return
        self._send(json.dumps(engine.snapshot()), "application/json")

    def log_message(self, *args):  # keep the terminal quiet
        pass


SERVER = None


def say_console(text):
    """print(), but quiet when there is no console (the packaged Windows app has none)."""
    try:
        if sys.stdout:
            print(text, flush=True)
    except Exception:
        pass


def already_running():
    """URL of a copy of this app that is already running, or None."""
    import urllib.request
    url = f"http://127.0.0.1:{PORT}"
    try:
        with urllib.request.urlopen(url + "/ping", timeout=1.5) as r:
            if json.loads(r.read().decode()).get("app") == APP_NAME:
                return url
    except Exception:
        pass
    return None


# ---------------- the user guide's text (guide.md) ----------------
USER_GUIDE_MD = """# Harmonarium: User Guide

Harmonarium writes out every ordering of the chords you choose, as engraved music. Pick a key, the chords to use and how many chords go in each progression; the app writes every possible progression, one per measure, as LilyPond score files, then engraves them into PDFs.

It's the companion to Melodarium and works the same way: the same Start, Pause, Stop and Resume controls, the same files, the same page layout.

## Contents

- [Quick start](#quick-start)
- [The window](#the-window)
- [Chords](#chords)
- [Progressions](#progressions)
- [Score](#score)
- [Pages and files](#pages-and-files)
- [Running, previewing and engraving](#running-previewing-and-engraving)
- [Reading the scores](#reading-the-scores)
- [What the app writes](#what-the-app-writes)
- [How big a run will be](#how-big-a-run-will-be)
- [Presets](#presets)
- [Troubleshooting](#troubleshooting)
- [License](#license)

## Quick start

1. Choose a **Key** and **Chord size** (triads, 7ths and so on). The key's seven chords appear under **Chords to use**, all ticked.
2. Untick any chords you don't want, or switch on **More chords** to add sus chords, secondary dominants, augmented sixths and others.
3. Set **Chords per permutation**: how many chords each progression has.
4. Check the summary at the top of the run card: it shows how many progressions, pages and files the run will make.
5. Press **Preview first page** to see the first page engraved.
6. Press **Start**. When the run finishes, press **Engrave PDFs**.

The defaults (the seven triads of C major, four chords per progression) make 2,401 progressions on about 150 pages.

## The window

The app opens in its own window. (If your computer is missing a part it needs, it opens in your web browser instead and says why under the title. Everything works the same either way.)

- **Settings** are on the left in five numbered cards, in the order you work: **1 Chords**, **2 Progressions**, **3 Score**, **4 Pages & files** and **5 Advanced**. Your saved presets are just above them.
- Click a card's heading to open or close it. A closed card shows a one-line summary of its settings, so you can check them without opening it. Chords and Progressions start open; the others start closed. The app remembers which cards you left open.
- Some cards have a sub-section below a dividing line, such as **Add a chord by hand…** and **Only part of the list…**: click it to open it.
- The **?** next to each card's title opens this guide at that section.
- **The run controls** (Start, Pause, Stop, Reset, progress, Preview, Engrave PDFs), the latest progressions and the list of finished files are on the right when the window is wide. In a narrower window they move below the settings, and a bar along the bottom shows the summary with **Preview** and **Start** buttons.
- **The Harmonarium logo** at the top left switches between dark and light mode. The app starts out following your system's setting; switching back to the look your system uses makes it follow the system again. The guide and Acknowledgements pages follow the same choice.
- **User guide** and **Acknowledgements** are under the Quit button. Acknowledgements lists everything the app includes, with licences: LilyPond and its components, the music fonts, the panel's font and Python.

## Chords

### Key

Choose the key note (17 choices, C to B, with both sharp and flat spellings) and the mode:

| Mode | Notes from C |
|---|---|
| Major | C D E F G A B |
| Natural minor | C D E♭ F G A♭ B♭ |
| Harmonic minor | C D E♭ F G A♭ B |
| Melodic minor | C D E♭ F G A B |
| Dorian | C D E♭ F G A B♭ |
| Phrygian | C D♭ E♭ F G A♭ B♭ |
| Lydian | C D E F♯ G A B |
| Mixolydian | C D E F G A B♭ |
| Locrian | C D♭ E♭ F G♭ A♭ B♭ |

The key name is shown on the right, for example "E♭ dorian".

### Chord size

**Triads, 7ths, 9ths, 11ths** or **13ths**. Each chord is built by stacking thirds from the notes of the key, so the chords change with the mode: in C major the 7ths are Imaj7, ii7, iii7, IVmaj7, V7, vi7 and viiø7.

### More chords

Each button adds a group of chords to the list. Hover over a button to see what it adds.

| Button | Adds |
|---|---|
| Inversions | Every key chord in 1st and 2nd inversion (and 3rd inversion for 7ths). Triads and 7ths only. |
| Sus chords | sus2 and sus4 on each degree where both notes belong to the key |
| Add9 | Major and minor triads with the key's 9th added |
| Secondary dominants | V of each major and minor chord except the tonic (V7 with 7ths and larger): V/ii, V/iii … |
| Borrowed chords | Chords from the parallel major or minor that aren't already in the key |
| Neapolitan | ♭II in root position and first inversion (♭IImaj7 with 7ths and larger) |
| Altered dominants | V7♭9, V7♯9 and V7♯5 |
| Augmented sixths | Italian, French, German and Swiss sixths on ♭6 |

The augmented sixths in C:

| Chord | Notes | Shown as | Sounds like |
|---|---|---|---|
| Italian | A♭ C F♯ | It+6 | A♭7 without its 5th |
| French | A♭ C D F♯ | Fr+6 | A♭7♭5 |
| German | A♭ C E♭ F♯ | Ger+6 | A♭7 |
| Swiss | A♭ C D♯ F♯ | Sw+6 | A♭7 (spelled with D♯) |

A chord that is already in the list is never added twice.

### Add a chord by hand

Open **Add a chord by hand…** (at the bottom of the Chords card) to add any chord: a root, one of 35 qualities (from major and minor through 7♯11 and 13ths), and optionally a bass note to make a slash chord such as C/E or Fm6/C. Press **Add**: the chord appears under "Added by hand", already ticked. Remove it with the × on its tag.

### Chords to use

Every chord available in the current key, grouped by where it came from. Each button shows the Roman numeral and, below it, the chord name. Click to tick or untick.

- **Key chords** ticks just the key's own chords. **Select all** and **Select none** do what they say.
- The tonic chord has a thin line under it.
- The ticked chords are permuted **in the order they appear in the list**, which sets the order of the progressions (see [Progressions](#progressions)).
- When you change the key, mode or chord size, the ticks follow the chords' positions: if ii and V were ticked in C major triads, ii7 and V7 are ticked when you switch to 7ths.

### How chords are named

Roman numerals are measured against the **major** scale on the key note, so in minor keys and modes the lowered degrees show a flat: in A minor the triads are i, ii°, ♭III, iv, v, ♭VI, ♭VII.

- Upper case is a major chord (or dominant), lower case is minor.
- **°** diminished, **ø** half-diminished, **+** augmented.
- Inversions use figured bass: **6** and **6 over 4** for triads, **6 over 5**, **4 over 3** and **4 over 2** for 7ths.
- Secondary dominants show their target: **V7/ii**.
- Chords added by hand with a slash bass show the bass's scale degree: **I/3** is C/E in C major.

Chord names spell every note correctly for the key, so a chord on the raised 4th is F♯, never G♭.

## Progressions

### Chords per permutation

From 2 to 12 chords in each progression. Above 8, a warning appears: the number of progressions grows very fast.

### Repeat rules

- **Repeats allowed** (both boxes empty): every chord can appear anywhere, any number of times.
- **No chord twice in a row**: skips progressions like I I V.
- **Use each chord once**: no chord appears twice anywhere in a progression. This needs at least as many ticked chords as chords per permutation.

Ticking one rule clears the other.

### Start and end

**Start on** and **End on** add a fixed chord before and/or after every permutation, for example start on I and end on V for half cadences. Choose "— nothing —" to leave either off. The repeat rules apply only to the permuted chords in between, so with "End on I" a progression can end I I.

When you change the key or chord size, these follow by position too (ii7 becomes ii).

### Range

The full set is every progression in order. To write only part of it, open **Only part of the list…** at the bottom of the Progressions card and pick a chord in each box for the **Start** and **End** progressions. The line above shows which progressions that is, for example "permutations 401–800 (400 of 2,401)". **Reset to full range** goes back to everything.

The End must come after the Start, and both must follow the repeat rules. If they don't, the boxes turn red and a message explains why.

### The order of the progressions

Progressions are listed like counting, using the order of **Chords to use**: with I, IV and V ticked and 3 chords each, the list starts I I I, I I IV, I I V, I IV I … and ends V V V. The repeat rules simply skip progressions they don't allow.

**Measure N is always progression N of the full set**, even in a ranged run, so the measure numbers in two separate runs never clash.

## Score

### Labels

- **Roman numerals**: below the staff.
- **Chord names**: above the staff.
- **Both** (the default): names above, numerals below.

On each line of music, all the numerals sit on one baseline and so do all the names, just clear of that line's own highest and lowest notes. So the labels stay close to the staff, and a line that climbs high or dips low moves only its own labels.

### Accidentals

- **Key signature** (the default): a key signature at the start of each line; accidentals hold for the measure.
- **On every note**: no key signature, and every note shows its sharp, flat or natural.

### Voicing

- **Close**: the chord tones packed as tightly as possible.
- **Drop 2**: the second note from the top moves down an octave.
- **Open**: every second note from the bottom moves up an octave, so C E G becomes C G E.

**Double the bass an octave below** adds the bass note again an octave lower. Inversions and slash chords always keep their bass note at the bottom.

Open voicing with a doubled bass spans a wide range. It reads best in the bass clef or at octave c, and fewer lines fit on a page.

### Chord placement

- **Root position**: every chord built up from its root (inversions and slash chords as written).
- **Smooth voice leading**: each measure starts with its first chord in root position; every following chord takes the inversion and octave that moves the notes least from the chord before it.

### Noteheads

**Filled**, **Hollow** or **Whole note**. This only changes how the heads look: every chord is still a quarter note, so spacing and the time signature stay the same.

### Clef and octave

Treble, bass, tenor or alto clef. **Octave** sets where the root (or the bass note of an inversion) sits: c, = C2, c = C3, c' = middle C (C4), c'' = C5, c''' = C6.

### Staff size

10 to 30 (LilyPond's default is 20). Larger staves fit fewer lines on a page.

### Chunk labels

A small label such as "I ii × ×" marks the first measure of each group of progressions that share their first two chords. It helps you find your place in a long run. Untick **Chunk labels** to leave them out.

## Pages and files

### Systems per page

- **Systems on the first page**: lines of music on the first page of each PDF, under the title. Default 6.
- **Systems on the other pages**: default 8.

A note appears above a slider when you go past 6 or 8, since pages start to look cramped. The app also works out how many systems really fit, from the highest and lowest notes your chords can reach (open voicing and smooth voice leading need more room) and the staff size. If you ask for more, a note below the slider says how many fit, and the scores use that many, so a page never spills its last lines onto a page of their own. The run's messages say so too.

### Pages per PDF and file size

- **Pages per PDF** (1 to 10,000): each PDF holds this many pages. Default 100.
- **Max file size** (500 to 1,500 KB): score files are split at this size. Smaller files engrave with less memory.

### PDF links

With **Links on chords** or **All links**, clicking a chord in the PDF opens its line in the score file in your text editor (if LilyPond's point-and-click is set up). Links make PDFs larger and store the folder's path inside them. Default: **No links**.

### Save to

Where each run's folder goes. By default that's next to the program, or Documents › Harmonarium when the program's folder can't be written to (always the case for the Mac app). Or choose **Another folder** and type a path or press **Browse…**.

### Plain-text lists

**Also save plain-text lists** writes each progression as a line of text, in the same files-and-ranges pattern as the scores. With labels set to **Both**, a line looks like:

```
Imaj7 ii7 V7 Imaj7  |  Gmaj7 Am7 D7 Gmaj7
```

Line N is progression N, matching measure N. The files are UTF-8 and use the real ♭, ♯, ° and ø.

### Advanced: LilyPond and fonts

These settings are in the **Advanced** card.

- **LilyPond program**: the installed app comes with LilyPond 2.26 built in (the status shows "bundled"), so there's nothing else to install. When you run the program file directly instead, it uses a LilyPond installed on your computer. To use a particular one, type the full path to the `lilypond` program and press **Use this**. **Find automatically** goes back to the built-in copy (or searching).
- **LilyPond version**: the score files are written in the syntax of **2.26 or newer** (default) or **2.24**. A red note appears if this doesn't match the LilyPond that was found.
- **Text font**: the font for titles, labels and measure numbers. Blank uses LilyPond's default. The box suggests fonts installed on your computer.
- **Music font**: the font for noteheads, clefs and accidentals. Blank uses Emmentaler, LilyPond's own. The installed app's LilyPond also has 13 more, the same as Melodarium: Beethoven, Cadence, Gonville, Gutenberg1939, Haydn, Improviso, LilyBoulez, LV GoldenAge, Paganini, Profondo, Ross, Scorlatti and Sebastiano. Pick one from the list. Other music fonts must be installed in LilyPond's own fonts folder; the app checks LilyPond's list and only asks before a run if the font isn't there.
- **Output music to outline**: draws music symbols as shapes, so the music font isn't embedded in the PDFs. PDFs become about 5 to 10 times larger. Cadence always uses it, because its licence (GPL) doesn't allow embedding it in documents; the box is ticked and locked for Cadence.

### The summary line

At the top of the run card, the summary shows the number of progressions, about how many pages and PDFs, the size of the score files and how many there will be. It turns amber for runs over 5 GB, and a red warning appears if the drive you're saving to doesn't have room.

## Running, previewing and engraving

### Start, Pause, Stop, Reset

- **Start** begins a run with the current settings. The settings lock while a run belongs to them.
- **Pause** holds the run in place; **Start** continues straight away.
- **Stop** ends the run and saves its place. **Resume** (the Start button, relabelled) carries on later, even after quitting and restarting the app.
- **Reset** forgets the saved run so you can change the settings.

The run saves its place about once a second. If something stops it (for example Windows briefly locking a file), the run is marked **stopped**, not lost, and **Resume** carries on from the same place. No progression is ever skipped or written twice.

The status card shows the progress, elapsed time, the chunk being written and the number of finished files. **Latest progressions** lists the last few progressions written.

### Preview first page

Engraves the first page with the current settings, without starting a run. In the app window it opens in your PDF app; in a browser it opens in a new tab. If LilyPond reports warnings or an error, they appear in a card under the run controls.

### Engrave PDFs

Turns the finished score files into PDFs with LilyPond, one file at a time so memory never fills up. Files whose PDFs are already up to date are skipped, so you can press it again after stopping. **Stop engraving** stops LilyPond and leaves the remaining files for later. If LilyPond crashes partway through a file, the app engraves that file's PDFs again one at a time. If a file still fails, the reasons are listed in plain English, and LilyPond's full log is saved next to the file.

You can also engrave outside the app with the `engrave_all` scripts in the run folder (see below).

### Quitting

Close the window, or press **Quit**. If a run or engraving is in progress the app asks first; the run's progress is saved either way. (In the browser, closing the tab leaves the app running in the background: press **Quit** to stop it.)

## Reading the scores

Each measure is one progression, with one chord per beat.

- **Above the staff**: chord names. **Below**: Roman numerals.
- **Measure numbers** sit by each barline, in italics. From one million they're shown in millions with six decimals (1,234,567 is 1.234567M); from one billion, in groups of three digits.
- **Chunk labels** (if on) sit above the chord names at the start of each group.
- **Title**: "Chord Permutations" (what the pages hold), with the repeat rule if one is set ("No Chord Twice in a Row").
- **Subtitle**: the chords per permutation, key, chord list (or count, when there are more than 16), start and end chords, voicing and placement.
- **Range line**: the file's first and last progression.
- **Footer**: the CC0 public domain dedication. The scores are yours to use freely.

Every line holds the same number of measures (fewer when chord labels are long), and every measure is spaced the same, including on the last page.

## What the app writes

Each run gets its own folder, named after its settings, for example:

```
len4-c-major-triads-I.ii.iii.IV.V.vi.viio-treble-c4
```

Other settings add to the name, such as `-norepeat`, `-from-ii-to-V`, `-drop2`, `-voiceleading`, `-hollow`, `-names` or `-from-401-to-800` for a range. Long chord lists are shortened to a count and a short code (`12chords-3f9a1c`).

Inside the folder:

| File | What it is |
|---|---|
| `I.I.I.I-V.V.IV.viio.ly` | A score file, named after its first and last progression (chord numerals joined by dots, ♭ as b, ♯ as s, ° as o, ø as h, + as x, / as _) |
| `….pdf` | The PDFs, once engraved: one per book of pages |
| `….txt` | Plain-text lists, if switched on |
| `index.csv` | Every PDF with its first and last progression, measures and pages |
| `master.ly` | Engraves the whole run in one go (fine for small runs) |
| `engrave_all.bat`, `engrave_all.command` | Double-click to engrave every file, one at a time (Windows, Mac) |
| `cc0-80x15.eps` | The CC0 badge used in the footer |

While a run is going, the file being written is `_in_progress.ly`. On Windows, if file paths would be too long, the last progression in file names is shortened to its final chords, like a page range "1234-56".

Two runs whose settings differ only in page layout (systems, pages per PDF, file size, PDF links, fonts) use the same folder name, so the second replaces the first's files. Use a different **Save to** folder to keep both.

## How big a run will be

The number of progressions, with n chords ticked and k chords per progression:

| Rule | Count | 7 chords, 4 each | 7 chords, 6 each |
|---|---|---|---|
| Repeats allowed | n to the power k | 2,401 | 117,649 |
| No chord twice in a row | n × (n − 1) to the power (k − 1) | 1,512 | 54,432 |
| Use each chord once | n × (n − 1) × … (k terms) | 840 | 5,040 |

Start and end chords don't change the count. Pages depend on how many measures fit on a line: two measures of 3 or 4 chords, four of 2 chords, one of 5 or more (or fewer when chord labels are long). At the default 8 lines per page, the defaults' 2,401 progressions take about 150 pages. The summary line always shows the estimate for your exact settings.

## Presets

At the top of the settings: type a name and press **Save** to store every setting, including the ticked chords and range. Choose a preset and press **Load** to bring it back, or **Delete** to remove it. Presets are kept in `chord_presets.json`.

## Troubleshooting

**"LilyPond wasn't found"**: in the installed app LilyPond is built in, so this means the app's build was interrupted: build it again. When running the program file directly, install LilyPond from lilypond.org, or open the **Advanced** card and type the full path to the `lilypond` program.

**"This LilyPond is 2.24…"**: set **LilyPond version** in the Advanced card to match the LilyPond you have.

**A music font error**: the font must be installed in LilyPond's own fonts folder (see LilyPond's "Replacing the notation font"), not just on your computer. The 13 fonts listed under [Advanced](#advanced-lilypond-and-fonts) are already there in the installed app.

**"Couldn't save … .pdf"**: the PDF is open in a viewer, and Windows can't replace an open file. Close it and press **Engrave PDFs** again.

**LilyPond ran out of memory**: lower **Pages per PDF** or **Max file size**, then engrave again.

**LilyPond crashed** (on Windows, an exit code such as 3221225477, which is error 0xC0000005): LilyPond itself stopped unexpectedly, which is usually a one-off. The app recovers on its own: it engraves each PDF in that file separately, trying each one twice, and keeps any PDFs that were already made. Only if a PDF still won't engrave is the file listed as failed; then lower **Pages per PDF** or **Max file size** and press **Engrave PDFs** again.

**"Stopped by an error … press Resume"**: the run stopped safely. Press **Resume** to carry on from the same place.

**The preview tab didn't open**: your browser blocked it. Use the **Open the preview** link in the card that appears.

**The app opened in the browser instead of its own window**: the line under the title says why. On Windows it's usually Microsoft's WebView2, which is free from developer.microsoft.com/microsoft-edge/webview2.

**Old score files still look the same after an update**: score files keep the layout they were written with. Press **Reset** and run again.

**Where the app keeps its own files**: in the same place as the runs by default (next to the program, or Documents › Harmonarium): `chord_progress.json` (the saved run), `chord_presets.json`, `chord_config.json` (the LilyPond path) and `window-data` (the window's remembered settings).

## License

Harmonarium is Copyright © 2026 Joshua Nichols. It is free software: you can redistribute it and/or modify it under the terms of the [GNU General Public License](https://www.gnu.org/licenses/gpl-3.0.html), version 3 or (at your option) any later version. The Harmonarium logo is licensed under the same terms.

Harmonarium comes with **no warranty**: it is distributed in the hope that it will be useful, but without even the implied warranty of merchantability or fitness for a particular purpose.

The source code is at [github.com/joshdnichols/Harmonarium](https://github.com/joshdnichols/Harmonarium), and the built apps' downloads include it too.

The GPL covers Harmonarium's own code and logo. It doesn't apply to your scores: they carry a [CC0 1.0](https://creativecommons.org/publicdomain/zero/1.0/) public domain dedication, so anyone may use them for anything. LilyPond, the music fonts, the panel's font (Academico), Python and the packages packed in with the app keep their own licenses, all listed on the **Acknowledgements** page.
"""

# ---------------- the user guide (Markdown, shown in the app) ----------------
import html as _html


def _md_slug(text):
    return re.sub(r"[^a-z0-9]+", "-", text.lower()).strip("-")


def _md_inline(text):
    """Inline Markdown: `code`, **bold**, *italic*, [text](url). Everything else is escaped."""
    out, pos = [], 0
    for m in re.finditer(r"`([^`]+)`", text):
        out.append(_md_inline_plain(text[pos:m.start()]))
        out.append("<code>" + _html.escape(m.group(1)) + "</code>")
        pos = m.end()
    out.append(_md_inline_plain(text[pos:]))
    return "".join(out)


def _md_inline_plain(text):
    t = _html.escape(text, quote=False)
    def link(m):
        label, url = m.group(1), m.group(2)
        if url.startswith("#"):
            return f'<a href="{url}">{label}</a>'
        return f'<a href="{url}" target="_blank" rel="noopener">{label}</a>'
    t = re.sub(r"\[([^\]]+)\]\(([^)\s]+)\)", link, t)
    t = re.sub(r"\*\*(.+?)\*\*", r"<strong>\1</strong>", t)
    t = re.sub(r"(?<![\w*])\*(?!\s)(.+?)(?<!\s)\*(?![\w*])", r"<em>\1</em>", t)
    return t


def markdown_to_html(md):
    """Just enough Markdown for the guide: headings (with anchors), paragraphs, lists,
    tables, code blocks."""
    lines, out, i = md.split("\n"), [], 0
    while i < len(lines):
        line = lines[i]
        if not line.strip():
            i += 1
            continue
        if line.startswith("```"):
            i += 1
            code = []
            while i < len(lines) and not lines[i].startswith("```"):
                code.append(lines[i])
                i += 1
            out.append("<pre><code>" + _html.escape("\n".join(code)) + "</code></pre>")
            i += 1
            continue
        m = re.match(r"(#{1,4})\s+(.*)", line)
        if m:
            level, text = len(m.group(1)), m.group(2).strip()
            out.append(f'<h{level} id="{_md_slug(text)}">{_md_inline(text)}</h{level}>')
            i += 1
            continue
        if line.startswith("|"):
            rows = []
            while i < len(lines) and lines[i].startswith("|"):
                rows.append([c.strip() for c in lines[i].strip().strip("|").split("|")])
                i += 1
            head, body = rows[0], [r for r in rows[1:] if not all(re.fullmatch(r":?-+:?", c) for c in r)]
            out.append('<div class="tablewrap"><table><thead><tr>'
                       + "".join(f"<th>{_md_inline(c)}</th>" for c in head) + "</tr></thead><tbody>"
                       + "".join("<tr>" + "".join(f"<td>{_md_inline(c)}</td>" for c in r) + "</tr>" for r in body)
                       + "</tbody></table></div>")
            continue
        m = re.match(r"(\s*)([-*]|\d+\.)\s+(.*)", line)
        if m:
            ordered = m.group(2)[0].isdigit()
            items = []
            while i < len(lines):
                m = re.match(r"\s*([-*]|\d+\.)\s+(.*)", lines[i])
                if not m:
                    if lines[i].startswith("  ") and lines[i].strip() and items:   # continued item
                        items[-1] += " " + lines[i].strip()
                        i += 1
                        continue
                    break
                items.append(m.group(2))
                i += 1
            tag = "ol" if ordered else "ul"
            out.append(f"<{tag}>" + "".join(f"<li>{_md_inline(t)}</li>" for t in items) + f"</{tag}>")
            continue
        para = []
        while i < len(lines) and lines[i].strip() and not re.match(r"(#{1,4}\s|```|\||\s*([-*]|\d+\.)\s)", lines[i]):
            para.append(lines[i].strip())
            i += 1
        out.append("<p>" + _md_inline(" ".join(para)) + "</p>")
    return "\n".join(out)


def guide_html():
    body = markdown_to_html(USER_GUIDE_MD)
    return ("<!doctype html><html lang='en'><head><meta charset='utf-8'>"
            "<meta name='viewport' content='width=device-width, initial-scale=1'>"
            "<title>Harmonarium: User Guide</title>"
            "<link rel='icon' href='/logo.svg' type='image/svg+xml'><script>try{var t=localStorage.getItem('harmonarium-theme');if(t==='dark'||t==='light')document.documentElement.dataset.theme=t;}catch(e){}</script><style>"
            "@font-face{font-family:'Academico';src:url('/fonts/Academico-Regular.otf') format('opentype');font-weight:400}"
            "@font-face{font-family:'Academico';src:url('/fonts/Academico-Bold.otf') format('opentype');font-weight:700}"
            ":root{--bg:#f6f5f2;--card:#fff;--ink:#1d1d1f;--muted:#6b6b70;--line:#e3e1dc;--accent:#2f6f5e;--soft:#e3efe9;"
            "--serif:'Academico',Georgia,'Times New Roman',serif}"
            "@media (prefers-color-scheme:dark){:root:not([data-theme=light]){--bg:#151517;--card:#1f1f22;--ink:#ececee;--muted:#9a9aa1;"
            "--line:#2e2e33;--accent:#5fb39b;--soft:#1f3530}}:root[data-theme=dark]{--bg:#151517;--card:#1f1f22;--ink:#ececee;--muted:#9a9aa1;"
            "--line:#2e2e33;--accent:#5fb39b;--soft:#1f3530}"
            "*{box-sizing:border-box}"
            "body{margin:0;background:var(--bg);color:var(--ink);font:16px/1.6 -apple-system,BlinkMacSystemFont,'Segoe UI',Roboto,sans-serif}"
            "main{max-width:780px;margin:0 auto;padding:32px 20px 80px}"
            "h1,h2,h3{font-family:var(--serif);font-variant-numeric:lining-nums;line-height:1.2;text-wrap:balance}"
            "h1{font-size:34px;margin:0 0 12px}"
            "h2{font-size:26px;margin:44px 0 10px;padding-top:18px;border-top:1px solid var(--line)}"
            "h3{font-size:19px;margin:26px 0 6px}"
            "p,li{max-width:68ch}ul,ol{padding-left:22px}li{margin:4px 0}"
            "a{color:var(--accent)}code{font:14px ui-monospace,Menlo,Consolas,monospace;background:var(--card);"
            "border:1px solid var(--line);border-radius:4px;padding:1px 5px}"
            "pre{background:var(--card);border:1px solid var(--line);border-radius:8px;padding:12px 14px;overflow-x:auto}"
            "pre code{border:0;padding:0;background:none}"
            ".tablewrap{overflow-x:auto;margin:12px 0}"
            "table{border-collapse:collapse;font-size:15px;min-width:60%}"
            "th,td{text-align:left;vertical-align:top;padding:7px 12px;border-bottom:1px solid var(--line)}"
            "th{font-size:13px;text-transform:uppercase;letter-spacing:.04em;color:var(--muted);font-weight:600}"
            "td:first-child{white-space:nowrap}"
            "h2:first-of-type + ul{columns:2;column-gap:32px;background:var(--card);border:1px solid var(--line);"
            "border-radius:10px;padding:14px 18px 14px 36px}"
            "@media (max-width:560px){h2:first-of-type + ul{columns:1}}"
            ".top{display:flex;justify-content:space-between;gap:12px;font-size:14px;margin-bottom:20px;color:var(--muted)}"
            "</style></head><body><main>"
            "<div class='top'><span>Harmonarium</span><a href='/guide.md' download='Harmonarium User Guide.md'>"
            "Save as Markdown</a></div>"
            + body + "</main></body></html>")


def open_guide_window(anchor=""):
    """App window: show the guide in a window of its own (the panel stays as it is)."""
    if WINDOW is None or WEBVIEW is None:
        return {"ok": False}
    url = f"http://127.0.0.1:{SERVER.server_address[1]}/guide" + (f"#{anchor}" if re.fullmatch(r"[a-z0-9-]*", anchor) and anchor else "")
    try:
        WEBVIEW.create_window(APP_NAME + " User Guide", url, width=900, height=900, min_size=(480, 400),
                              background_color="#f6f5f2", text_select=True)
    except TypeError:
        WEBVIEW.create_window(APP_NAME + " User Guide", url, width=900, height=900)
    except Exception as e:
        return {"ok": False, "error": str(e)}
    return {"ok": True}


# ---------------- the app window (pywebview), with the browser as a fallback ----------------
# The control panel is a web page served by this program. When pywebview is installed (and,
# on Windows, Microsoft's WebView2 runtime is present) it is shown in the program's own window;
# otherwise it opens in the default browser exactly as before.
WEBVIEW = None        # the pywebview module, once the window is in use
WINDOW = None         # the app window
WINDOW_NOTE = ""      # shown in the panel when it had to open in the browser instead
WEBVIEW2_CLIENT = r"Microsoft\EdgeUpdate\Clients\{F3017226-FE2A-4295-8BDF-00C3A9A7E4C5}"
WEBVIEW2_DOWNLOAD = "https://developer.microsoft.com/microsoft-edge/webview2/"


def webview2_installed():
    """Windows: is Microsoft's WebView2 runtime installed? Checks the registry entry
    Microsoft documents for this (its 'pv' version value, per machine or per user)."""
    if sys.platform != "win32":
        return True
    try:
        import winreg
    except ImportError:
        return False
    places = [(winreg.HKEY_LOCAL_MACHINE, "SOFTWARE\\WOW6432Node\\" + WEBVIEW2_CLIENT),
              (winreg.HKEY_LOCAL_MACHINE, "SOFTWARE\\" + WEBVIEW2_CLIENT),
              (winreg.HKEY_CURRENT_USER, "Software\\" + WEBVIEW2_CLIENT)]
    for root, path in places:
        try:
            with winreg.OpenKey(root, path) as key:
                version, _ = winreg.QueryValueEx(key, "pv")
            if version and version != "0.0.0.0":
                return True
        except OSError:
            continue
    return False


def window_backend():
    """(pywebview module, "") when the app window can be used, else (None, why not)."""
    if "--browser" in sys.argv[1:] or os.environ.get("HARMONARIUM_BROWSER"):
        return None, ""
    try:
        import webview
    except Exception:
        return None, ("Running in your browser. For the app's own window, install pywebview "
                      "(pip install pywebview) and start the app again.")
    if not webview2_installed():
        return None, ("Running in your browser: the app window needs Microsoft Edge WebView2 Runtime, "
                      "which isn't installed on this computer. It's free from " + WEBVIEW2_DOWNLOAD)
    return webview, ""


def window_busy():
    return (engine is not None and engine.status in ("running", "paused")) or engraver.status == "running"


def run_window(webview, url, owns_server=True):
    """Show the panel in its own window; returns when the window closes. Raises if the
    window can't be created (the caller then falls back to the browser)."""
    global WINDOW, WEBVIEW
    try:
        webview.settings["OPEN_EXTERNAL_LINKS_IN_BROWSER"] = True
    except Exception:
        pass
    kwargs = dict(width=1280, height=900, min_size=(720, 560), background_color="#f6f5f2", text_select=True)
    try:
        window = webview.create_window(APP_NAME, url, **kwargs)
    except TypeError:                       # an older pywebview without some of these options
        window = webview.create_window(APP_NAME, url, width=1280, height=900)
    if owns_server:
        def on_closing():
            # closing the window quits the app; ask first if a run or engraving is going
            if not window_busy():
                return True
            try:
                return bool(window.create_confirmation_dialog(
                    "Quit " + APP_NAME + "?",
                    "A run or engraving is in progress. Quitting stops it; the run's progress is "
                    "saved, so Resume carries on from the same place next time."))
            except Exception:
                return True
        def on_closed():
            # the guide's window (if open) closes with the main one, so the program can end
            for other in list(getattr(webview, "windows", []) or []):
                if other is not window:
                    try:
                        other.destroy()
                    except Exception:
                        pass
        try:
            window.events.closing += on_closing
            window.events.closed += on_closed
        except Exception:
            pass
        WINDOW, WEBVIEW = window, webview
    storage = os.path.join(DATA_DIR, "window-data")    # keeps the panel's remembered open sections
    try:
        webview.start(private_mode=False, storage_path=storage)
    except TypeError:
        webview.start()


def open_with_system(path):
    """Open a file in its default app (the PDF viewer for a preview)."""
    if sys.platform == "win32":
        os.startfile(path)                                   # noqa: the Windows default app
    elif sys.platform == "darwin":
        subprocess.Popen(["open", path])
    else:
        subprocess.Popen(["xdg-open", path])


def open_preview_in_viewer():
    """Copy the latest preview to a fresh name and open it in the default PDF app. (A viewer
    may lock the file it shows; the copy keeps preview.pdf free for the next preview.)"""
    src = os.path.join(PREVIEW_DIR, "preview.pdf")
    if not os.path.exists(src):
        return {"ok": False, "error": "There's no preview yet. Press Preview first page."}
    dst = os.path.join(PREVIEW_DIR, f"Harmonarium preview {time.strftime('%H.%M.%S')}.pdf")
    try:
        shutil.copyfile(src, dst)
        open_with_system(dst)
    except Exception as e:
        return {"ok": False, "error": f"Couldn't open a PDF viewer ({e}). The preview is at: {src}"}
    return {"ok": True, "path": dst}


def native_folder_dialog():
    """The window's own folder picker, or None if it isn't available."""
    if WINDOW is None or WEBVIEW is None:
        return None
    kind = getattr(getattr(WEBVIEW, "FileDialog", None), "FOLDER", None)
    if kind is None:
        kind = getattr(WEBVIEW, "FOLDER_DIALOG", None)
    if kind is None:
        return None
    try:
        result = WINDOW.create_file_dialog(kind)
    except Exception:
        return None
    if not result:
        return {"path": ""}                                  # cancelled
    return {"path": result[0] if isinstance(result, (list, tuple)) else str(result)}


def main():
    global engine, SERVER, WINDOW_NOTE
    if len(sys.argv) >= 3 and sys.argv[1] == "--pick-folder":
        pick_folder(sys.argv[2])
        return
    webview, note = window_backend()
    running = already_running()
    if running:                       # opened again: show the panel of the copy that's running
        if webview:
            try:
                run_window(webview, running, owns_server=False)
                return
            except Exception:
                pass
        webbrowser.open(running)
        return
    engine = Engine()
    threading.Thread(target=installed_fonts, daemon=True).start()   # warm the font list
    threading.Thread(target=find_lilypond, daemon=True).start()     # look for LilyPond
    try:
        server = ThreadingHTTPServer(("127.0.0.1", PORT), Handler)
    except OSError:
        server = ThreadingHTTPServer(("127.0.0.1", 0), Handler)  # port busy: pick any free one
    SERVER = server
    url = f"http://127.0.0.1:{server.server_address[1]}"
    serving = threading.Thread(target=server.serve_forever, daemon=True)
    serving.start()
    try:
        if webview:
            try:
                run_window(webview, url)          # returns when the window is closed
                return
            except Exception as e:
                globals()["WINDOW"] = None
                note = (f"Running in your browser: the app window couldn't open ({e}).")
        WINDOW_NOTE = note
        say_console(f"Control panel: {url}")
        say_console("Leave this window open while it runs. Quit from the panel (or Ctrl+C here).")
        threading.Timer(0.5, lambda: webbrowser.open(url)).start()
        while serving.is_alive():
            serving.join(0.5)
    except KeyboardInterrupt:
        pass
    finally:
        engraver.stop()
        engine.stop()                         # saves progress
        try:
            server.shutdown()
        except Exception:
            pass
        server.server_close()
        say_console("\nSaved. Goodbye.")


if __name__ == "__main__":
    main()
