# Mathematics in Lean


## Numbers


1. **Nat: Natural Numbers**: 1, 2, 3, 4, 5, ...
   - Example: Number of apples in a basket: 1, 2, 3, ...

2. **Whole Numbers**: 0, 1, 2, 3, 4, ...
   - Example: Counting the number of students absent in a class: 0, 1, 2, 3, ...
   - def Whole := {n :  ℤ | n  ≥  0}

3. **Integers**: ..., -3, -2, -1, 0, 1, 2, 3, ...
   - Example: Temperatures below zero: -5°C, -10°C, -15°C, ...

4. **Rational Numbers**: Fractions and decimals that can be expressed as a quotient of integers.
   - Example: \( \frac{3}{4} \), \( -\frac{2}{5} \), \( 0.25 \)

5. **Irrational Numbers**: Numbers that cannot be expressed as fractions and have non-repeating, non-terminating decimal representations.
   - Example: \( \sqrt{2} \), \( \pi \), \( e \)

6. **Real Numbers**: All rational and irrational numbers.
   - Example: \( \frac{3}{4} \), \( -\frac{2}{5} \), \( \sqrt{2} \), \( \pi \)

7. **Complex Numbers**: Numbers with a real part and an imaginary part.
   - Example: \( 3 + 2i \), \( -1 - i \), \( 2i \)


## Overview

This tutorial depends on Lean 4, VS Code, and Mathlib.
You can find the textbook both online and in this repository
in
[html format](https://leanprover-community.github.io/mathematics_in_lean/)
or as a
[pdf document](https://leanprover-community.github.io/mathematics_in_lean/mathematics_in_lean.pdf).
The book is designed to be read as you
work through examples and exercises,
using a copy of this repository on your computer.
Alternatively, you can use Github Codespaces or Gitpod to run Lean and VS Code in the cloud.

This version of *Mathematics in Lean* is designed for [Lean 4](https://leanprover.github.io/) and
[Mathlib](https://github.com/leanprover-community/mathlib4).
For the Lean 3 version, see [https://github.com/leanprover-community/mathematics_in_lean3](https://github.com/leanprover-community/mathematics_in_lean3).


## To use this repository on your computer

Do the following:

1. Install Lean 4 and VS Code following
   these [instructions](https://leanprover-community.github.io/get_started.html).

2. Make sure you have [git](https://git-scm.com/) installed.

3. Follow these [instructions](https://leanprover-community.github.io/install/project.html#working-on-an-existing-project)
   to fetch the `mathematics_in_lean` repository and open it up in VS Code.

4. Each section in the textbook has an associated Lean file with examples and exercises.
   You can find them in the folder `MIL`, organized by chapter.
   We strongly recommend making a copy of that folder and experimenting and doing the
   exercises in that copy.
   This leaves the originals intact, and it also makes it easier to update the repository as it changes (see below).
   You can call the copy `my_files` or whatever you want and use it to create
   your own Lean files as well.

At that point, you can open the textbook in a side panel in VS Code as follows:

1. Type `ctrl-shift-P` (`command-shift-P` in macOS).

2. Type `Lean 4: Docview: Open Docview` in the bar that appears, and then
  press return. (You can press return to select it as soon as it is highlighted
  in the menu.)

3. In the window that opens, click on `Open documentation of current project`.

The textbook and this repository are still a work in progress.
You can update the repository by typing `git pull`
followed by `lake exe cache get` inside the `mathematics_in_lean` folder.
(This assumes that you have not changed the contents of the `MIL` folder,
which is why we suggested making a copy.)


## To use this repository with Github Codespaces

If you have trouble installing Lean, you can use Lean directly in your browser using Github
Codespaces.
This requires a Github account. If you are signed in to Github, click here:

<a href='https://codespaces.new/leanprover-community/mathematics_in_lean' target="_blank" rel="noreferrer noopener"><img src='https://github.com/codespaces/badge.svg' alt='Open in GitHub Codespaces' style='max-width: 100%;'></a>

Make sure the Machine type is `4-core`, and then press `Create codespace`
(this might take a few minutes).
This creates a virtual machine in the cloud,
and installs Lean and Mathlib.

Opening any `.lean` file in the MIL folder will start Lean,
though this may also take a little while.
We suggest making a copy of the `MIL` directory, as described
in the instructions above for using MIL on your computer.
You can update the repository by opening a terminal in the browser
and typing `git pull` followed by `lake exe cache get` as above.

Codespaces offers a certain number of free hours per month. When you are done working,
press `Ctrl/Cmd+Shift+P` on your keyboard, start typing `stop current codespace`, and then
select `Codespaces: Stop Current Codespace` from the list of options.
If you forget, don't worry: the virtual machine will stop itself after a certain
amount of time of inactivity.

To restart a previous workspace, visit <https://github.com/codespaces>.


## To use this repository with Gitpod

Gitpod is an alternative to Github Codespaces, but is a little less convenient,
since it requires you to verify your phone number.
If you have a Gitpod account or are willing to sign up for one,
point your browser to
[https://gitpod.io/#/https://github.com/leanprover-community/mathematics_in_lean](https://gitpod.io/#/https://github.com/leanprover-community/mathematics_in_lean).
This creates a virtual machine in the cloud,
and installs Lean and Mathlib.
It then presents you with a VS Code window, running in a virtual
copy of the repository.
We suggest making a copy of the `MIL` directory, as described
in the instructions above for using MIL on your computer.
You can update the repository by opening a terminal in the browser
and typing `git pull` followed by `lake exe cache get` as above.

Gitpod gives you 50 free hours every month.
When you are done working, choose `Stop workspace` from the menu on the left.
The workspace should also stop automatically
30 minutes after the last interaction or 3 minutes after closing the tab.

To restart a previous workspace, go to [https://gitpod.io/workspaces/](https://gitpod.io/workspaces/).
If you change the filter from Active to All, you will see all your recent workspaces.
You can pin a workspace to keep it on the list of active ones.


## Contributing

PRs and issues should be opened at the upstream
[source repository](https://github.com/avigad/mathematics_in_lean_source).
