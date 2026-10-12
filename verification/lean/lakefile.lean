import Lake
open Lake DSL

package BiplanarC5

/-- the encoder, the drawings, the colourings and the finite reduction -/
@[default_target]
lean_lib BiplanarC5

/-- `biplanar-dump w out.cnf` writes the formula `Φ(w)` in DIMACS form -/
lean_exe «biplanar-dump» where
  root := `Main
