import BiplanarC5.Drawing

namespace Biplanar

/-- `col` is a proper colouring of `C_k[w]` with colours below `K` -/
def IsColouring (w : List Nat) (K : Nat) (col : List Nat) : Bool :=
  col.length == (bags w).length && col.all (· < K) &&
    (blowupEdges w).all fun (u, v) => col[u]! != col[v]!

end Biplanar
