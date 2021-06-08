# lean4-maze

This repo shows how maze solving
can be encoded as theorem proving
using the Lean 4 programming language.

It draws inspration from https://github.com/kbuzzard/maze-game.


## How To Play

First, install Lean 4 on your computer: https://leanprover.github.io/lean4/doc/setup.html

Then open `Maze.lean` in emacs or VSCode.

You can define a maze like this:

```lean
def maze := ┌────────┐
            │▓▓▓▓▓▓▓▓│
            │▓░▓@▓░▓▓│
            │▓░▓░░░▓▓│
            │▓░░▓░▓▓▓│
            │▓▓░▓░▓░░│
            │▓░░░░▓░▓│
            │▓░▓▓▓▓░▓│
            │▓░░░░░░▓│
            │▓▓▓▓▓▓▓▓│
            └────────┘
```

The `@` symbol denotes your current location.
You are free to move within the `░` cells.
The `▓` cells are walls.

Your goal is to escape the maze at any of its borders.

You can interactively solve a maze like this:


```lean
example : can_escape maze :=
 by south
    east
    south
    south
```

As you make progress, Lean's goal view will display your current state.
For example, after the moves made above, the state is shown as:

```lean
⊢ can_escape
    (
        ┌────────┐
        │▓▓▓▓▓▓▓▓│
        │▓░▓░▓░▓▓│
        │▓░▓░░░▓▓│
        │▓░░▓░▓▓▓│
        │▓▓░▓@▓░░│
        │▓░░░░▓░▓│
        │▓░▓▓▓▓░▓│
        │▓░░░░░░▓│
        │▓▓▓▓▓▓▓▓│
        └────────┘
        )
```

The main moves available to you at any point are `north`, `south`, `east`, and `west`.

When you reach the boundary, you can finish your proof with `out`.

## how does it work?

As you traverse a maze, you are constructing a proof
that the maze satisfies the `can_escape` predicate, defined as

```lean
def can_escape (state : GameState) : Prop :=
  ∃ (gs : List Move), is_win (List.foldl make_move state gs)
```

The mazes as drawn above are actual valid Lean 4 syntax!

We define new syntax categories and some `macro_rules` for elaborating
them into valid values.

To get Lean to render the values back in the above format,
we define a delaboration function and register it with the pretty printer.

Lean 4 lets us do all of this in-line, in ordinary Lean 4 code.

