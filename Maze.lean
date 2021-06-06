import Lean

declare_syntax_cat game_cell
declare_syntax_cat game_cell_sequence
declare_syntax_cat game_row
declare_syntax_cat horizontal_border
declare_syntax_cat game_top_row
declare_syntax_cat game_bottom_row

syntax "═" : horizontal_border

syntax "\n╔" horizontal_border* "╗\n" : game_top_row

syntax "╚" horizontal_border* "╝\n" : game_bottom_row

syntax "░" : game_cell -- empty
syntax "▓" : game_cell -- wall
syntax "@" : game_cell -- player

syntax "║" game_cell* "║\n" : game_row

syntax:max game_top_row game_row* game_bottom_row : term

-- helper syntax for intermediate parser values
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

-- size, current row, remaining cells -> gamestate
def game_state_from_cells_aux : Coords → Nat → List (List CellContents) → GameState
| size, _, [] => ⟨size, ⟨0,0⟩, []⟩
| size, currentRow, row::rows =>
        let prevState := game_state_from_cells_aux size (currentRow + 1) rows
        update_state_with_row currentRow row prevState

-- size, remaining cells -> gamestate
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


inductive Move where
  | east  : Move
  | west  : Move
  | north : Move
  | south : Move

@[simp]
def make_move : GameState → Move → GameState
| ⟨s, ⟨x,y⟩, w⟩, Move.east =>
             if w.notElem ⟨x+1, y⟩ ∧ x + 1 ≤ s.x
             then ⟨s, ⟨x+1, y⟩, w⟩
             else ⟨s, ⟨x,y⟩, w⟩
| ⟨s, ⟨x,y⟩, w⟩, Move.west =>
             if w.notElem ⟨x-1, y⟩
             then ⟨s, ⟨x-1, y⟩, w⟩
             else ⟨s, ⟨x,y⟩, w⟩
| ⟨s, ⟨x,y⟩, w⟩, Move.north =>
             if w.notElem ⟨x, y-1⟩
             then ⟨s, ⟨x, y-1⟩, w⟩
             else ⟨s, ⟨x,y⟩, w⟩
| ⟨s, ⟨x,y⟩, w⟩, Move.south =>
             if w.notElem ⟨x, y + 1⟩ ∧ y + 1 ≤ s.y
             then ⟨s, ⟨x, y+1⟩, w⟩
             else ⟨s, ⟨x,y⟩, w⟩

def is_win : GameState → Prop
| ⟨⟨sx, sy⟩, ⟨x,y⟩, w⟩ => x = 0 ∨ y = 0 ∨ x + 1 = sx ∨ y + 1 = sy

def can_escape (state : GameState) : Prop :=
  ∃ (gs : List Move), is_win (List.foldl make_move state gs)

theorem can_still_escape (g : GameState) (m : Move) (hg : can_escape (make_move g m)) : can_escape g :=
 have ⟨pms, hpms⟩ := hg
 Exists.intro
  (m::pms)
  (by have h' : List.foldl make_move g (m :: pms) =
                     List.foldl make_move (make_move g m) pms := rfl
      rw [h']
      exact hpms)

theorem step_west
  {s: Coords}
  {x y : Nat}
  {w: List Coords}
  (hclear' : w.notElem ⟨x,y⟩)
  (W : can_escape ⟨s,⟨x,y⟩,w⟩) :
  can_escape ⟨s,⟨x+1,y⟩,w⟩ :=
   by have hmm : GameState.mk s ⟨x,y⟩ w = make_move ⟨s,⟨x+1, y⟩,w⟩ Move.west :=
               by simp
                  have h' : x + 1 - 1 = x := rfl
                  rw [h', hclear']
                  simp
      rw [hmm] at W
      exact can_still_escape ⟨s,⟨x+1,y⟩,w⟩ Move.west W

theorem step_east
  {s: Coords}
  {x y : Nat}
  {w: List Coords}
  (hclear' : w.notElem ⟨x+1,y⟩)
  (hinbounds : x + 1 ≤ s.x)
  (E : can_escape ⟨s,⟨x+1,y⟩,w⟩) :
  can_escape ⟨s,⟨x, y⟩,w⟩ :=
    by have hmm : GameState.mk s ⟨x+1,y⟩ w = make_move ⟨s, ⟨x,y⟩,w⟩ Move.east :=
         by simp
            rw [hclear']
            simp [hinbounds]
       rw [hmm] at E
       exact can_still_escape ⟨s, ⟨x,y⟩, w⟩ Move.east E

theorem step_north
  {s: Coords}
  {x y : Nat}
  {w: List Coords}
  (hclear' : w.notElem ⟨x,y⟩)
  (N : can_escape ⟨s,⟨x,y⟩,w⟩) :
  can_escape ⟨s,⟨x, y+1⟩,w⟩ :=
    by have hmm : GameState.mk s ⟨x,y⟩ w = make_move ⟨s,⟨x, y+1⟩,w⟩ Move.north :=
         by simp
            have h' : y + 1 - 1 = y := rfl
            rw [h', hclear']
            simp
       rw [hmm] at N
       exact can_still_escape ⟨s,⟨x,y+1⟩,w⟩ Move.north N

theorem step_south
  {s: Coords}
  {x y : Nat}
  {w: List Coords}
  (hclear' : w.notElem ⟨x,y+1⟩)
  (hinbounds : y + 1 ≤ s.y)
  (S : can_escape ⟨s,⟨x,y+1⟩,w⟩) :
  can_escape ⟨s,⟨x, y⟩,w⟩ :=
    by have hmm : GameState.mk s ⟨x,y+1⟩ w = make_move ⟨s,⟨x, y⟩,w⟩ Move.south :=
            by simp
               rw [hclear']
               simp [hinbounds]
       rw [hmm] at S
       exact can_still_escape ⟨s,⟨x,y⟩,w⟩ Move.south S

def escape_west {sx sy : Nat} {y : Nat} {w : List Coords} : can_escape ⟨⟨sx, sy⟩,⟨0, y⟩,w⟩ :=
    ⟨[], Or.inl rfl⟩

def escape_east {sy x y : Nat} {w : List Coords} : can_escape ⟨⟨x+1, sy⟩,⟨x, y⟩,w⟩ :=
  ⟨[], Or.inr $ Or.inr $ Or.inl rfl⟩

def escape_north {sx sy : Nat} {x : Nat} {w : List Coords} : can_escape ⟨⟨sx, sy⟩,⟨x, 0⟩,w⟩ :=
  ⟨[], Or.inr $ Or.inl rfl⟩

def escape_south {sx x y : Nat} {w: List Coords} : can_escape ⟨⟨sx, y+1⟩,⟨x, y⟩,w⟩ :=
  ⟨[], Or.inr $ Or.inr $ Or.inr rfl⟩

-- the `rfl`s are to discharge the `hclear` and `hinbounds` side-goals
macro "west" : tactic => `(apply step_west; rfl)
macro "east" : tactic => `(apply step_east; rfl; rfl)
macro "north" : tactic => `(apply step_north; rfl)
macro "south" : tactic => `(apply step_south; rfl; rfl)


-- Define an "or" tactic combinator, like <|> in Lean 3.
elab t1:tactic " ⟨|⟩ " t2:tactic : tactic =>
   do try Lean.Elab.Tactic.evalTactic t1
      catch err => Lean.Elab.Tactic.evalTactic t2

elab "fail_out" : tactic => throwError "not currently at maze boundary"

macro "out" : tactic => `(apply escape_north ⟨|⟩ apply escape_south ⟨|⟩
                           apply escape_east ⟨|⟩ apply escape_west ⟨|⟩ fail_out)

---------------------------
-- Now we will define a delaborator that will cause GameState to be rendered as a maze.

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

partial def extractWallList : Lean.Expr → Lean.PrettyPrinter.Delaborator.DelabM (List Coords)
| exp => do
  let exp':Lean.Expr ← (Lean.Meta.whnf exp)
  let f := Lean.Expr.getAppFn exp'
  if f.constName!.toString == "List.cons"
  then let consArgs := Lean.Expr.getAppArgs exp'
       let rest ← extractWallList consArgs[2]
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

-- The attribute [delab] registers this function as a delaborator for the GameState.mk constructor.
@[delab app.GameState.mk] def delabGameState : Lean.PrettyPrinter.Delaborator.Delab := do
  let e ← Lean.PrettyPrinter.Delaborator.getExpr
  let e' ← (Lean.Meta.whnf e)
  guard $ e'.getAppNumArgs == 3
  let gameStateArgs := Lean.Expr.getAppArgs e'
  let ⟨numCols, numRows⟩ ← extractXY gameStateArgs[0]
  let playerCoords ← extractXY gameStateArgs[1]
  let walls'' ← extractWallList gameStateArgs[2]

  let topBarCell ← `(horizontal_border| ═)
  let topBar := Array.mkArray numCols topBarCell
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

-- We register the same elaborator for applications of the game_state_from_cells function.
@[delab app.game_state_from_cells] def delabGameState' : Lean.PrettyPrinter.Delaborator.Delab := delabGameState

--------------------------

-- Can escape the trivial maze in any direction.
example : can_escape ╔═╗
                     ║@║
                     ╚═╝ := by out


-- some other mazes with immediate escapes
example : can_escape ╔══╗
                     ║  ║
                     ║@ ║
                     ║  ║
                     ╚══╝ := by out
example : can_escape ╔══╗
                     ║  ║
                     ║ @║
                     ║  ║
                     ╚══╝ := by out
example : can_escape ╔═══╗
                     ║ @ ║
                     ║   ║
                     ║   ║
                     ╚═══╝ := by out
example : can_escape ╔═══╗
                     ║   ║
                     ║   ║
                     ║ @ ║
                     ╚═══╝ := by out


-- Now for some more interesting mazes.

def maze1 := ╔══════╗
             ║▓▓▓▓▓▓║
             ║▓░░@░▓║
             ║▓░░░░▓║
             ║▓░░░░▓║
             ║▓▓▓▓░▓║
             ╚══════╝

example : can_escape maze1 := by
  west
  west
  east
  south
  south
  east
  east
  south
  out

def maze2 := ╔════════╗
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

example : can_escape maze2 :=
 by south
    east
    south
    south
    south
    west
    west
    west
    south
    south
    east
    east
    east
    east
    east
    north
    north
    north
    east
    out

def maze3 := ╔════════════════════════════╗
             ║▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓║
             ║▓░░░░░░░░░░░░░░░░░░░░▓░░░@░▓║
             ║▓░▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓░▓░▓▓▓▓▓║
             ║▓░▓░░░▓░░░░▓░░░░░░░░░▓░▓░░░▓║
             ║▓░▓░▓░▓░▓▓▓▓░▓▓▓▓▓▓▓▓▓░▓░▓░▓║
             ║▓░▓░▓░▓░▓░░░░▓░░░░░░░░░░░▓░▓║
             ║▓░▓░▓░▓░▓░▓▓▓▓▓▓▓▓▓▓▓▓░▓▓▓░▓║
             ║▓░▓░▓░▓░░░▓░░░░░░░░░░▓░░░▓░▓║
             ║▓░▓░▓░▓▓▓░▓░▓▓▓▓▓▓▓▓▓▓░▓░▓░▓║
             ║▓░▓░▓░░░░░▓░░░░░░░░░░░░▓░▓░▓║
             ║▓░▓░▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓░▓║
             ║░░▓░░░░░░░░░░░░░░░░░░░░░░░░▓║
             ║▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓║
             ╚════════════════════════════╝

example : can_escape maze3 :=
 by west
    west
    west
    south
    admit -- can you finish the proof?
