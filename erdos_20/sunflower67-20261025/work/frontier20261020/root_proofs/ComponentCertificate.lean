import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic
namespace FrontierComponentCertificate

def firstTen : List Nat := [7,11,21,26,28,38,41,44,49,50]
def firstTwenty : List Nat := firstTen ++ firstTen.map (fun t => t * 64)
def labelledDesigns : List (List Nat) :=
  [[7,11,21,26,28,38,41,44,49,50],[7,11,22,25,28,37,42,44,49,50],[7,13,19,26,28,38,41,42,49,52],[7,13,22,25,26,35,42,44,49,52],[7,14,19,25,28,37,41,42,50,52],[7,14,21,25,26,35,41,44,50,52],[11,13,19,22,28,37,38,42,49,56],[11,13,21,22,26,35,38,44,49,56],[11,14,19,21,28,37,38,41,50,56],[11,14,21,22,25,35,37,44,50,56],[13,14,19,21,26,35,38,41,52,56],[13,14,19,22,25,35,37,42,52,56]]

def supportPositions (b : Nat) : List Nat :=
  (List.range 13).filter (fun i => b.testBit i)

def canonicalPositions (b : Nat) : List Nat :=
  let p := supportPositions b
  p ++ (List.range (6 - p.length)).map (fun i => 13+i)

def liftTriple (p : List Nat) (t : Nat) : Nat :=
  ((List.range 6).filter (fun i => t.testBit i)).foldl (fun s i => s + 2 ^ p[i]!) 0

def component (b : Nat) (d : List Nat) : List Nat := d.map (liftTriple (canonicalPositions b))

def compatible (r : Nat) (s : Nat) : Bool :=
  firstTwenty.all (fun t => !((t &&& s == t &&& r) && (t &&& s == s &&& r)))

def componentAllowed (r b : Nat) (d : List Nat) : Bool :=
  (component b d).all (compatible r)

def allSupports : List Nat := (List.range 8192).filter (fun b => (supportPositions b).length ≤ 6)

def noComponent (r : Nat) : Bool :=
  allSupports.all (fun b => labelledDesigns.all (fun d => !(componentAllowed r b d)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem no_split_two_two : noComponent 195 = true := by decide
end FrontierComponentCertificate
#print axioms FrontierComponentCertificate.no_split_two_two
