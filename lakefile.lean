import Lake

open Lake DSL

package maze

require aesop from git "https://github.com/leanprover-community/aesop" @ "v4.4.0"


@[default_target]
lean_lib Maze
