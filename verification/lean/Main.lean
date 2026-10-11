import BiplanarC5.Encode

/-- `biplanar-dump 1,1,7,1,7 out.cnf` writes `Biplanar.encode [1, 1, 7, 1, 7]` in DIMACS form. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | [ws, out] =>
    let w := (ws.splitOn ",").map String.toNat!
    let f := Biplanar.encode w
    IO.FS.writeFile out (Std.Sat.CNF.dimacs f)
    IO.println s!"{w}: {f.clauses.size} clauses, {f.numLiterals} variables"
    return 0
  | _ =>
    IO.eprintln "usage: biplanar-dump w1,w2,w3,w4,w5 out.cnf"
    return 1
