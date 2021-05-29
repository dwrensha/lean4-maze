import Lean

/-
a maze looks like:

╔═══════╗
║▓▓▓▓▓▓▓║
║▓░▓@▓░▓║
║▓░▓░░░▓║
║▓░░▓░▓▓║
║▓▓░▓░▓▓║
║▓░░░░▓▓║
║▓░▓▓▓▓▓║
╚═══════╝

-/

declare_syntax_cat game_cell
declare_syntax_cat game_cell_sequence
declare_syntax_cat game_row
declare_syntax_cat horizontal_border
declare_syntax_cat game_top_row
declare_syntax_cat game_bottom_row

syntax "═" : horizontal_border

syntax "\n╔" horizontal_border* "╗\n" : game_top_row

syntax "╚" horizontal_border* "╝\n" : game_bottom_row

syntax "░" : game_cell
syntax "▓" : game_cell
syntax "@" : game_cell

syntax "║" game_cell* "║\n" : game_row

syntax game_top_row game_row* game_bottom_row : term

syntax "╣{" game_row* "}╠" : term
syntax "╣" game_cell* "╠" : term

-- x is column number
-- y is row number
-- upper left is ⟨0,0⟩
structure Coords where
  x : Nat
  y : Nat

structure GameState where
  size : Coords
  position : Coords
  walls: List Coords


inductive CellContents where
  | empty  : CellContents
  | wall  : CellContents
  | player : CellContents

--
def game_state_from_cells : Coords → List (List CellContents) → GameState
| size, [] => ⟨size, ⟨0,0⟩, []⟩
| size, _ => ⟨size, ⟨0,0⟩, []⟩ -- TODO


macro_rules
| `(╣╠) => `(([] : List CellContents))
| `(╣░ $cells:game_cell*╠) => `(CellContents.empty :: ╣$cells:game_cell*╠)
| `(╣▓ $cells:game_cell*╠) => `(CellContents.wall :: ╣$cells:game_cell*╠)
| `(╣@ $cells:game_cell*╠) => `(CellContents.player :: ╣$cells:game_cell*╠)

macro_rules
| `(╣{}╠) => `(([] : List (List CellContents)))
| `(╣{ ║$cells:game_cell*║  $rows:game_row*}╠) => `(╣$cells:game_cell*╠ :: ╣{$rows:game_row*}╠)

macro_rules
| `(╔ $tb:horizontal_border* ╗
    $rows:game_row*
    ╚ $bb:horizontal_border* ╝) =>
      let rsize := Lean.Syntax.mkNumLit (toString rows.size) -- there's gotta be a better way to do this
      let csize := Lean.Syntax.mkNumLit (toString tb.size) -- there's gotta be a better way to do this
      `( game_state_from_cells ⟨$csize,$rsize⟩ ╣{$rows:game_row*}╠ )

#check Array.size


#reduce ╔═══════╗
        ║▓▓▓▓▓▓▓║
        ║▓░▓@▓░▓║
        ║▓░▓░░░▓║
        ║▓░░▓░▓▓║
        ║▓▓░▓░▓▓║
        ║▓░░░░▓▓║
        ║▓░▓▓▓▓▓║
        ╚═══════╝


@[delab app.GameState.mk] def delabGameState : Lean.PrettyPrinter.Delaborator.Delab := do
  let e ← Lean.PrettyPrinter.Delaborator.getExpr
  guard $ e.getAppNumArgs == 3
  let pexpr:Lean.Expr ← Lean.PrettyPrinter.Delaborator.withAppFn
           $ Lean.PrettyPrinter.Delaborator.withAppFn
           $ Lean.PrettyPrinter.Delaborator.withAppArg Lean.PrettyPrinter.Delaborator.getExpr
  let position':Lean.Expr ← (Lean.Meta.whnf pexpr)
  let positionArgs := Lean.Expr.getAppArgs position'
  let numCols := (Lean.Expr.natLit? positionArgs[0]).get!
  let numRows := (Lean.Expr.natLit? positionArgs[1]).get!
  let topBarCell ← `(horizontal_border| ═)
  let topBar := Array.mkArray numCols topBarCell
  let emptyCell ← `(game_cell| ░)
  let emptyRow := Array.mkArray numCols emptyCell
  let emptyRowStx ← `(game_row|║$emptyRow:game_cell*║)
  let allRows := Array.mkArray numRows emptyRowStx

  `(╔$topBar:horizontal_border*╗
    $allRows:game_row*
    ╚$topBar:horizontal_border*╝)

#reduce ╔═══════╗
        ║▓▓▓▓▓▓▓║
        ║▓░▓@▓░▓║
        ║▓░▓░░░▓║
        ║▓░░▓░▓▓║
        ║▓▓░▓░▓▓║
        ║▓░░░░▓▓║
        ║▓░▓▓▓▓▓║
        ╚═══════╝

