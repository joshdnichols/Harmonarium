# Harmonarium: User Guide

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

All the numerals in a run sit on one baseline, and so do all the names, the same on every line and page. The heights are worked out once for the whole run, from the highest and lowest notes any of its chords can reach.

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

A note appears above a slider when you go past 6 or 8, since pages start to look cramped. A red warning appears below it if LilyPond probably can't fit that many: it would then spill lines onto extra pages.

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

Turns the finished score files into PDFs with LilyPond, one file at a time so memory never fills up. Files whose PDFs are already up to date are skipped, so you can press it again after stopping. **Stop engraving** stops LilyPond and leaves the remaining files for later. If a file fails, the reasons are listed in plain English, and LilyPond's full log is saved next to the file.

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

**"Stopped by an error … press Resume"**: the run stopped safely. Press **Resume** to carry on from the same place.

**The preview tab didn't open**: your browser blocked it. Use the **Open the preview** link in the card that appears.

**The app opened in the browser instead of its own window**: the line under the title says why. On Windows it's usually Microsoft's WebView2, which is free from developer.microsoft.com/microsoft-edge/webview2.

**Old score files still look the same after an update**: score files keep the layout they were written with. Press **Reset** and run again.

**Where the app keeps its own files**: in the same place as the runs by default (next to the program, or Documents › Harmonarium): `chord_progress.json` (the saved run), `chord_presets.json`, `chord_config.json` (the LilyPond path) and `window-data` (the window's remembered settings).
