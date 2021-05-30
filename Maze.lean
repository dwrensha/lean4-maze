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
deriving BEq

instance : ToString Coords where
  toString := (λ ⟨x,y⟩ => String.join ["Coords.mk ", toString x, ", ", toString y])

structure GameState where
  size : Coords
  position : Coords
  walls: List Coords

inductive CellContents where
  | empty  : CellContents
  | wall  : CellContents
  | player : CellContents

def update_state_with_row_aux : Nat → Nat → List CellContents → GameState → GameState
| currentRowNum, currentColNum, [], oldState => oldState
| currentRowNum, currentColNum, cell::contents, oldState =>
             let oldState' := update_state_with_row_aux currentRowNum (currentColNum+1) contents oldState
             match cell with
             | CellContents.empty => oldState'
             | CellContents.wall => {size     := oldState'.size,
                                     position := oldState'.position,
                                     walls    := ⟨currentColNum,currentRowNum⟩::oldState'.walls}
             | CellContents.player => {size     := oldState'.size,
                                       position := ⟨currentColNum,currentRowNum⟩,
                                       walls    := oldState'.walls}

def update_state_with_row : Nat → List CellContents → GameState → GameState
| currentRowNum, rowContents, oldState => update_state_with_row_aux currentRowNum 0 rowContents oldState

-- size, current row, remaining cells -> gamestatem
def game_state_from_cells_aux : Coords → Nat → List (List CellContents) → GameState
| size, _, [] => ⟨size, ⟨0,0⟩, []⟩
| size, currentRow, row::rows =>
        let prevState := game_state_from_cells_aux size (currentRow + 1) rows
        update_state_with_row currentRow row prevState

-- size, remaining cells -> gamestatem
def game_state_from_cells : Coords → List (List CellContents) → GameState
| size, cells => game_state_from_cells_aux size 0 cells

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

def allowed_move : GameState → GameState → Bool
| ⟨s, ⟨x,y⟩, w⟩, ⟨s', ⟨x',y'⟩, w'⟩ =>
      w == w' ∧                -- walls are static
      s == s' ∧                -- size is static
      w.notElem ⟨x', y'⟩ ∧ -- not allowed to enter wall
      ((x == x' ∧ (y == y' + 1 ∨ y + 1 == y')) ||
       (y == y' ∧ (x == x' + 1 ∨ x + 1 == x')))

def is_win : GameState → Bool
| ⟨⟨sx, sy⟩, ⟨x,y⟩, w⟩ => x == 0 ∨ y == 0 ∨ x + 1 == sx ∨ y + 1 == sy

def ends_with_win : List GameState → Bool
| [] => false
| g :: [] => is_win g
| g :: gs => ends_with_win gs

theorem still_ends_with_win (gs: List GameState) (h: ends_with_win gs) (g: GameState) :
  ends_with_win (g::gs) = true :=
by simp
   admit

def consecutive_pairs {α : Type} : List α → List (α × α)
| [] => []
| a::[] => []
| a1::a2::rest => ⟨a1, a2⟩ :: consecutive_pairs rest

def all_moves_allowed (gs: List GameState) : Bool :=
  (consecutive_pairs gs).all (λ(g1,g2)=> allowed_move g1 g2)

theorem all_moves_still_allowed
  {g0 : GameState}
  {gs : List GameState}
  (h : all_moves_allowed (g0::gs))
  (g : GameState)
  (hg : allowed_move g g0) :
  all_moves_allowed (g::gs) :=
by admit

def can_win (state : GameState) : Prop :=
  ∃ (gs : List GameState), ends_with_win gs ∧ all_moves_allowed gs

theorem step_left
  {s: Coords}
  {x y : Nat}
  {w: List Coords}
  (hclear : w.contains ⟨x+1,y⟩ == false)
  (hclear' : w.contains ⟨x,y⟩ == false)
  (h : can_win ⟨s,⟨x,y⟩,w⟩) :
  can_win ⟨s,⟨x+1, y⟩,w⟩ :=
  let g := GameState.mk s ⟨x,y⟩ w
  let gs := h.1
  ⟨ g::gs,
    still_ends_with_win gs h.2.1 g,
    match gs with
    | [] => by rfl
    | g'::gs' =>
           let hg : allowed_move g g' = true := sorry
           sorry
   ⟩


theorem step_right
  {s: Coords}
  {x y : Nat}
  {w: List Coords}
  (hclear : w.contains ⟨x,y⟩ == false)
  (hclear' : w.contains ⟨x+1,y⟩ == false)
  (h : can_win ⟨s,⟨x+1,y⟩,w⟩) :
  can_win ⟨s,⟨x, y⟩,w⟩ := sorry

theorem step_up
  {s: Coords}
  {x y : Nat}
  {w: List Coords}
  (hclear : w.contains ⟨x,y+1⟩ == false)
  (hclear' : w.contains ⟨x,y⟩ == false)
  (h : can_win ⟨s,⟨x,y⟩,w⟩) :
  can_win ⟨s,⟨x, y+1⟩,w⟩ := sorry

theorem step_down
  {s: Coords}
  {x y : Nat}
  {w: List Coords}
  (hclear : w.contains ⟨x,y⟩ == false)
  (hclear' : w.contains ⟨x,y+1⟩ == false)
  (h : can_win ⟨s,⟨x,y+1⟩,w⟩) :
  can_win ⟨s,⟨x, y⟩,w⟩ := sorry


def escape_west
  {s : Coords}
  {y: Nat}
  {w: List Coords} :
  can_win ⟨s,⟨0, y⟩,w⟩ := sorry

def escape_east
  {sy x y : Nat}
  {w: List Coords} :
  can_win ⟨⟨x+1, sy⟩,⟨x, y⟩,w⟩ := sorry

def escape_north
  {s : Coords}
  {x : Nat}
  {w: List Coords} :
  can_win ⟨s,⟨x, 0⟩,w⟩ := sorry

def escape_south
  {sx x y : Nat}
  {w: List Coords} :
  can_win ⟨⟨sx, y+1⟩,⟨x, y⟩,w⟩ := sorry


macro "west" : tactic => `(apply step_left; rfl; rfl)
macro "east" : tactic => `(apply step_right; rfl; rfl)
macro "north" : tactic => `(apply step_up; rfl; rfl)
macro "south" : tactic => `(apply step_down; rfl; rfl)


def extractXY : Lean.Expr → Lean.PrettyPrinter.Delaborator.DelabM Coords
| e => do
  let e':Lean.Expr ← (Lean.Meta.whnf e)
  let sizeArgs := Lean.Expr.getAppArgs e'
  let f := Lean.Expr.getAppFn e'
  let x ← Lean.Meta.whnf sizeArgs[0]
  let y ← Lean.Meta.whnf sizeArgs[1]
  let numCols := (Lean.Expr.natLit? x).get!
  let numRows := (Lean.Expr.natLit? y).get!
  Coords.mk numCols numRows

def extractWallList : Nat -> Lean.Expr → Lean.PrettyPrinter.Delaborator.DelabM (List Coords)
| 0, _ => [] -- recursion deptch reached.
| (depth+1), exp => do
  let exp':Lean.Expr ← (Lean.Meta.whnf exp)
  let f := Lean.Expr.getAppFn exp'
  if f.constName!.toString == "List.cons"
  then let consArgs := Lean.Expr.getAppArgs exp'
       let rest ← extractWallList depth consArgs[2]
       let ⟨wallCol, wallRow⟩ ← extractXY consArgs[1]
       (Coords.mk wallCol wallRow) :: rest
  else [] -- "List.nil"

def update2dArray {α : Type} : Array (Array α) → Coords → α → Array (Array α)
| a, ⟨x,y⟩, v =>
   Array.set! a y $ Array.set! (Array.get! a y) x v

def update2dArrayMulti {α : Type} : Array (Array α) → List Coords → α → Array (Array α)
| a, [], v => a
| a, c::cs, v =>
     let a' := update2dArrayMulti a cs v
     update2dArray a' c v

def delabGameRow : (Array Lean.Syntax) → Lean.PrettyPrinter.Delaborator.DelabM Lean.Syntax
| a => do `(game_row| ║ $a:game_cell* ║)

@[delab app.GameState.mk] def delabGameState : Lean.PrettyPrinter.Delaborator.Delab := do
  let e ← Lean.PrettyPrinter.Delaborator.getExpr
  let e' ← (Lean.Meta.whnf e)
  guard $ e'.getAppNumArgs == 3
  let sizeExpr:Lean.Expr ← Lean.PrettyPrinter.Delaborator.withAppFn
           $ Lean.PrettyPrinter.Delaborator.withAppFn
           $ Lean.PrettyPrinter.Delaborator.withAppArg Lean.PrettyPrinter.Delaborator.getExpr
  let ⟨numCols, numRows⟩ ← extractXY sizeExpr

  let positionExpr:Lean.Expr ← Lean.PrettyPrinter.Delaborator.withAppFn
           $ Lean.PrettyPrinter.Delaborator.withAppArg Lean.PrettyPrinter.Delaborator.getExpr
  let playerCoords ← extractXY positionExpr

  let topBarCell ← `(horizontal_border| ═)
  let topBar := Array.mkArray numCols topBarCell

  let wallsExpr:Lean.Expr ← Lean.PrettyPrinter.Delaborator.withAppArg Lean.PrettyPrinter.Delaborator.getExpr
  let walls':Lean.Expr ← (Lean.Meta.whnf wallsExpr)

  let walls'' ← extractWallList 1000000 walls'

  let playerCell ← `(game_cell| @)
  let emptyCell ← `(game_cell| ░)
  let wallCell ← `(game_cell| ▓)
  let emptyRow := Array.mkArray numCols emptyCell
  let emptyRowStx ← `(game_row|║$emptyRow:game_cell*║)
  let allRows := Array.mkArray numRows emptyRowStx

  let a0 := Array.mkArray numRows $ Array.mkArray numCols emptyCell
  let a1 := update2dArray a0 playerCoords playerCell
  let a2 := update2dArrayMulti a1 walls'' wallCell
  let aa ← Array.mapM delabGameRow a2

  `(╔$topBar:horizontal_border*╗
    $aa:game_row*
    ╚$topBar:horizontal_border*╝)

def maze1 := ╔════════╗
             ║▓▓▓▓▓▓▓▓║
             ║▓░▓@▓░▓▓║
             ║▓░▓░░░▓▓║
             ║▓░░▓░▓▓▓║
             ║▓▓░▓░▓░░║
             ║▓░░░░▓░▓║
             ║▓░▓▓▓▓░▓║
             ║▓░░░░░░▓║
             ║▓▓▓▓▓▓▓▓║
             ╚════════╝

def maze2 := ╔══════╗
             ║▓▓▓▓▓▓║
             ║▓░░@░▓║
             ║▓░░░░▓║
             ║▓░░░░▓║
             ║▓▓▓▓░▓║
             ╚══════╝

example : can_win maze2 := by
  west
  west
  east
  west
  south
  south
  east
  east
  east
  south
  apply escape_south



