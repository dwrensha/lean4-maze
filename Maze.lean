import Lean

structure GameState where
  position : Nat
  goal : Nat
--  size : Nat

inductive CellContents where
  | empty  : CellContents
  | player : CellContents
  | goal   : CellContents

--
def game_state_from_cells : List CellContents → GameState
 | [] => ⟨0,0⟩
 | CellContents.empty::cells => let ⟨p,g⟩ := game_state_from_cells cells
                                ⟨p+1, g+1⟩
 | CellContents.player::cells => let ⟨p,g⟩ := game_state_from_cells cells
                                ⟨0, g+1⟩
 | CellContents.goal::cells =>  let ⟨p,g⟩ := game_state_from_cells cells
                                ⟨p+1, 0⟩

#reduce game_state_from_cells [CellContents.goal, CellContents.player, CellContents.empty, CellContents.empty]

declare_syntax_cat game_cell
declare_syntax_cat game_cell_sequence

syntax "┤" game_cell_sequence "├ ": term

syntax "┤{" game_cell_sequence "}├": term

syntax "★" : game_cell
syntax "░" : game_cell
syntax "@" : game_cell

syntax game_cell* : game_cell_sequence

macro_rules
| `(┤{}├) => `(([] : List CellContents))
| `(┤{░ $cells:game_cell* }├) => `( CellContents.empty :: ┤{$cells:game_cell*}├)
| `(┤{★ $cells:game_cell* }├) => `( CellContents.goal :: ┤{$cells:game_cell*}├)
| `(┤{@ $cells:game_cell* }├) => `( CellContents.player :: ┤{$cells:game_cell*}├)

macro_rules
| `(┤$cells:game_cell*├) => `(game_state_from_cells  ┤{$cells:game_cell*}├ )

#reduce ┤░@░★░░├

#check GameState.mk

@[appUnexpander GameState] def unexpandGameState : Lean.PrettyPrinter.Unexpander
--  | `({ position := $p, goal := $g}) => `(┤░@░★░░├)
  | `(GameState $p $g) => `(┤░@░░░░★░░├)
  | _              => throw ()

#reduce ┤░@░★░░├

def allowed_move : GameState → GameState → Prop
| ⟨n, g⟩, ⟨m, h⟩ => (m + 1 = n ∧ g = h) ∨ (m = n + 1 ∧ g = h)

def is_win : GameState → Prop
| ⟨n, m⟩ => n = m

def can_win (g : GameState) : Prop :=
  ∃ (n : Nat),
  ∃ (m : Nat → GameState),
  (g = m n) ∧
  (is_win (m 0)) ∧
  (∀ (i : Nat), i < n → allowed_move (m i) (m (i + 1)))

theorem done {n : Nat} : can_win ⟨n,n⟩ := sorry

theorem step_left {p g : Nat} (h : can_win ⟨p, g⟩) : can_win ⟨p + 1, g⟩ :=
  let n := h.1 + 1
  ⟨n,
   λ i => sorry,
   by admit,
   by admit,
   λ i h => by admit⟩

theorem step_right {p g : Nat} (h : can_win ⟨p + 1, g⟩) : can_win ⟨p, g⟩ := sorry

example : can_win {position := 11, goal := 7} :=
by apply step_left
   apply step_left
   apply step_left
   apply step_left
   exact done

example : can_win {position := 9, goal := 11} :=
by apply step_right
   apply step_right
   exact done
