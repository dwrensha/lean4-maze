import Lean

structure GameState where
  position : Nat
  goal : Nat

declare_syntax_cat game_cell
declare_syntax_cat game_cell_sequence

syntax "┤" game_cell_sequence "├ ": term

syntax "★" : game_cell
syntax "░" : game_cell
syntax "@" : game_cell

syntax game_cell* : game_cell_sequence

macro_rules
| `(┤├) => `((⟨1, 3⟩ : GameState))
| `(┤$cell:game_cell $cells:game_cell*├) => `((⟨2, 3⟩ : GameState))
--| `(┤░░├) => `((⟨1, 3⟩ : GameState))

#check ┤░░░░├

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
