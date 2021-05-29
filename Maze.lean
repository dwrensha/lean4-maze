import Lean
--import Lean.PrettyPrinter.Delaborator.Basic

namespace OneDimension

structure GameState where
  position : Nat
  goal : Nat
  size : Nat

inductive CellContents where
  | empty  : CellContents
  | player : CellContents
  | goal   : CellContents

--
def game_state_from_cells : List CellContents → GameState
 | [] => ⟨0,0,0⟩
 | CellContents.empty::cells => let ⟨p,g,s⟩ := game_state_from_cells cells
                                ⟨p+1, g+1,s+1⟩
 | CellContents.player::cells => let ⟨p,g,s⟩ := game_state_from_cells cells
                                ⟨0, g+1, s+1⟩
 | CellContents.goal::cells =>  let ⟨p,g, s⟩ := game_state_from_cells cells
                                ⟨p+1, 0, s+1⟩

#reduce game_state_from_cells [CellContents.goal, CellContents.player, CellContents.empty, CellContents.empty]

declare_syntax_cat game_cell'

syntax "┤" game_cell'* "├ ": term

syntax "┤{" game_cell'* "}├": term

syntax "★" : game_cell'
syntax "░" : game_cell'
syntax "@" : game_cell'

macro_rules
| `(┤{}├) => `(([] : List CellContents))
| `(┤{░ $cells:game_cell'* }├) => `( CellContents.empty :: ┤{$cells:game_cell'*}├)
| `(┤{★ $cells:game_cell'* }├) => `( CellContents.goal :: ┤{$cells:game_cell'*}├)
| `(┤{@ $cells:game_cell'* }├) => `( CellContents.player :: ┤{$cells:game_cell'*}├)

macro_rules
| `(┤$cells:game_cell'*├) => `(game_state_from_cells  ┤{$cells:game_cell'*}├ )

#reduce ┤░@░★░░├

@[delab app.OneDimension.GameState.mk] def delabGameState : Lean.PrettyPrinter.Delaborator.Delab := do
  let e ← Lean.PrettyPrinter.Delaborator.getExpr
  guard $ e.getAppNumArgs == 3
  let g ← Lean.PrettyPrinter.Delaborator.withAppFn
           $ Lean.PrettyPrinter.Delaborator.withAppArg Lean.PrettyPrinter.Delaborator.delab
  let s ← Lean.PrettyPrinter.Delaborator.withAppArg Lean.PrettyPrinter.Delaborator.delab
  let e ← `(game_cell'| ░)
  let player ← `(game_cell'| @)
  let goalc ← `(game_cell'| ★)
  let pexpr:Lean.Expr ← Lean.PrettyPrinter.Delaborator.withAppFn
           $ Lean.PrettyPrinter.Delaborator.withAppFn
           $ Lean.PrettyPrinter.Delaborator.withAppArg Lean.PrettyPrinter.Delaborator.getExpr
  let position' ← (Lean.Meta.whnf pexpr)
  let position : Nat := (Lean.Expr.natLit? position').get!
  let goal : Nat := g.isNatLit?.get!
  let size : Nat := s.isNatLit?.get!
  let a0 := Array.mkArray size e
  let a1 := Array.set! a0 position player
  let a2 := Array.set! a1 goal goalc
  `(┤$a2:game_cell'*├)

#reduce ┤░░@░★░░░░░░├

#check GameState.mk (1 + 2) 5 10

def allowed_move : GameState → GameState → Prop
| ⟨n, g, s⟩, ⟨m, h, t⟩ => (m + 1 = n ∧ g = h) ∨ (m = n + 1 ∧ g = h)

def is_win : GameState → Prop
| ⟨n, m, _⟩ => n = m

def can_win (g : GameState) : Prop :=
  ∃ (n : Nat),
  ∃ (m : Nat → GameState),
  (g = m n) ∧
  (is_win (m 0)) ∧
  (∀ (i : Nat), i < n → allowed_move (m i) (m (i + 1)))

theorem done {n s: Nat} : can_win ⟨n,n,s⟩ := sorry

theorem step_left {p g s: Nat} (h : can_win ⟨p, g, s⟩) : can_win ⟨p + 1, g, s⟩ :=
  let n := h.1 + 1
  ⟨n,
   λ i => sorry,
   by admit,
   by admit,
   λ i h => by admit⟩

theorem step_right {p g s: Nat} (h : can_win ⟨p + 1, g, s⟩) : can_win ⟨p, g, s⟩ := sorry

example : can_win {position := 11, goal := 7, size := 15} :=
by apply step_left
   apply step_left
   apply step_left
   apply step_left
   exact done

example : can_win {position := 9, goal := 11, size := 15} :=
by apply step_left
   apply step_right
   apply step_right
   apply step_right
   exact done

end OneDimension

-----------------------------------------------------

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

syntax "╔" horizontal_border* "╗\n" : game_top_row

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
      `( game_state_from_cells ⟨0,0⟩ ╣{$rows:game_row*}╠ )


#reduce ╔═══════╗
        ║▓▓▓▓▓▓▓║
        ║▓░▓@▓░▓║
        ║▓░▓░░░▓║
        ║▓░░▓░▓▓║
        ║▓▓░▓░▓▓║
        ║▓░░░░▓▓║
        ║▓░▓▓▓▓▓║
        ╚═══════╝
