import Lean
import BiplanarC5

/-!
# Axiom audit

Every theorem of the library may use only `propext`, `Classical.choice` and `Quot.sound`; the drawings,
the colourings and the reduction are checked by kernel evaluation (`decide +kernel`), so no
`native_decide` occurs here. The certificates of Theorem 5.1 are checked separately by
`scripts/certify.sh`, one weight vector at a time.
-/

open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let names := env.constants.fold (init := #[]) fun acc n ci =>
    if (`Biplanar).isPrefixOf n && (match ci with | .thmInfo _ => true | _ => false) then
      acc.push n else acc
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut bad : Array Name := #[]
  for n in names do
    let axs ← liftCoreM <| collectAxioms n
    if axs.any (fun a => !allowed.contains a) then bad := bad.push n
  if bad.isEmpty then
    logInfo m!"axiom audit: {names.size} theorems, all within propext, Classical.choice, Quot.sound"
  else
    logError m!"axiom audit failed for {bad}"

-- Lemma 2.2: the 26 and 36 classes
#print axioms Biplanar.cands17_spec
#print axioms Biplanar.wits16_spec
-- Lemma 2.1 by enumeration
#print axioms Biplanar.entries_lt_8
#print axioms Biplanar.reduction
-- Proposition 2.3: two of the 36 drawings, and an 8-colouring
#print axioms Biplanar.biplanar_3_3_3_3_4
#print axioms Biplanar.biplanar_1_1_6_1_7
#print axioms Biplanar.colouring_3_3_3_3_4
