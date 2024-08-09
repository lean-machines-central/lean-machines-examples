# LeanMachines examples

Example specifications for the LeanMachines modelling framework

## Overview

LeanMachines is a library for the Lean4 programming language and proof
assistant dedicated to the formal modeling of stateful systems.

The main repository is at: https://github.com/lean-machines-central/lean-machines

This repository contains a selection of example specifications:

 - The Buffer example from the IFM2024 LeanMachines paper (module `Buffer`)

 - From Event-B :
   * the Bridge example of the Event-B book (module `EventB.Bridge`)
   * the Courses example of the Event-B tutorial (module `EventB.Courses`)

 - From VDM:
   * the Alarm System example of the VDM Book (module `VDM.AlarmSystem`)

**Important**: these are rather "liberal" interpretations of the original models

## Getting started

To experiment with the LeanMachines framework and examples, the first requirement is to install the Lean4 proof assistant and the Mathlib4 library, see: <https://leanprover-community.github.io/get_started.html>

The examples can be compiled using the lake tool :

```
$ lake build 
...
```

This can take a relatively long time for the first build, or when Mathlib4 receives a large update.

Because of the Mathlib4 dependency, it may be required to update the `lean-toolchain` file:

```
$ lake update
...
$ cp .lake/packages/mathlib/lean-toolchain .
```
(please see the Mathlib4 documentation for details)

The recommended way to experiment with the examples is to "play" with them
using lean4-enabled editor: either *vscode* or *emacs*
(editor support for Lean4 is discussed in the Lean4 documentation).

## Authors and acknowledgment

The main author is Frederic Peschanski,  Sorbonne University

## License

The software is licensed (C) 2024 Frédéric Peschanski
under the Apache License 2.0  (the same as Lean4 and Mathlib4). Please see the `LICENSE` file.

