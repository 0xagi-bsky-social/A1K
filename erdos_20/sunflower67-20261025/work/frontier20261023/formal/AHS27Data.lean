import SunflowerLean.Erdos20TripleWitness
import SunflowerLean.Erdos20RankThree
import SunflowerLean.Erdos20FiniteReduction

/-! The Abbott–Hanson 27-block configuration and its isolation property.
Finite facts use kernel reduction. The ambient isolation theorem quantifies over
arbitrary types and does not assume an ambient support bound. -/
namespace FrontierAHS27

set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

/-- Three consecutive groups of three points. -/
def group (i : Fin 3) : Finset (Fin 9) :=
  Finset.univ.filter (fun x => x.val / 3 = i.val)

/-- Choose two points in each of two of the three groups. -/
def AHS : Finset (Finset (Fin 9)) :=
  {{0,1,3,4},
   {0,1,3,5},
   {0,1,4,5},
   {0,2,3,4},
   {0,2,3,5},
   {0,2,4,5},
   {1,2,3,4},
   {1,2,3,5},
   {1,2,4,5},
   {0,1,6,7},
   {0,1,6,8},
   {0,1,7,8},
   {0,2,6,7},
   {0,2,6,8},
   {0,2,7,8},
   {1,2,6,7},
   {1,2,6,8},
   {1,2,7,8},
   {3,4,6,7},
   {3,4,6,8},
   {3,4,7,8},
   {3,5,6,7},
   {3,5,6,8},
   {3,5,7,8},
   {4,5,6,7},
   {4,5,6,8},
   {4,5,7,8}}

theorem AHS_card : AHS.card = 27 := by decide +kernel
#print AHS_card

theorem AHS_uniform : ∀ S ∈ AHS, S.card = 4 := by decide +kernel
#print AHS_uniform

theorem AHS_intersecting :
    ∀ S ∈ AHS, ∀ T ∈ AHS, (S ∩ T).Nonempty := by decide +kernel


end FrontierAHS27
