import SunflowerLean.Erdos20Tetrahedron

/-! The classical sharp rank-three, three-petal upper bound.
This does not establish the uniform exponential bound in arbitrary rank. -/
namespace Erdos20SharpTwenty
open Erdos20SharpTriples Erdos20GraphEquality Erdos20Tetrahedron

/-- Two degree-six points in a member force the stronger bound nineteen. -/
theorem card_le_nineteen_of_two_degree_six_vertices
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (x y z : α)
    (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3)
    (hxyz : ({x,y,z} : Finset α) ∈ F)
    (hxdeg : (F.filter (fun S => x ∈ S)).card = 6)
    (hydeg : (F.filter (fun S => y ∈ S)).card = 6) : F.card ≤ 19 := by
  obtain ⟨w,hxy,hxz,hyz,hxw,hyw,hzw,hxyw,hxzw,hyzw⟩ :=
    two_degree_six_vertices_force_tetrahedron F x y z hu hf hxyz hxdeg hydeg
  have hK4 : ({x,y,z,w} : Finset α).card = 4 := by
    simp [hxy,hxz,hyz,hxw,hyw,hzw]
  have hfaces := tetrahedron_faces_subset_of_four_members F x y z w
    hxy hxz hxw hyz hyw hzw hxyz hxyw hxzw hyzw
  have hD := tetrahedron_disjoint_card_le_three F x y z w hu hf
    hxy hxz hyz hxw hyw hzw hxyz hxyw hxzw hyzw hxdeg
  exact card_le_nineteen_of_tetrahedron_disjoint_card_le_three F {x,y,z,w}
    hu hf hK4 hfaces hD

/-- Every three-uniform family without a three-petal sunflower has at most twenty members. -/
theorem rank_three_three_petals_card_le_twenty
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3) : F.card ≤ 20 := by
  have hb := rank_three_three_petals_card_le_twenty_one F hu hf
  by_contra hnot
  have hc : F.card = 21 := by omega
  obtain ⟨R,hR,hdeg⟩ := card_twenty_one_exists_all_degree_six_member F hu hf hc
  obtain ⟨x,y,z,_hxy,_hxz,_hyz,hRshape⟩ := Finset.card_eq_three.mp (hu R hR)
  have hxyz : ({x,y,z} : Finset α) ∈ F := by simpa only [hRshape] using hR
  have hxdeg : (F.filter (fun S => x ∈ S)).card = 6 := hdeg x (by simp [hRshape])
  have hydeg : (F.filter (fun S => y ∈ S)).card = 6 := hdeg y (by simp [hRshape])
  have h19 := card_le_nineteen_of_two_degree_six_vertices F x y z hu hf hxyz hxdeg hydeg
  omega

/-- An extremal twenty-member family cannot have two degree-six points in one member. -/
theorem twenty_members_no_two_degree_six_in_member
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (x y z : α)
    (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3)
    (hc : F.card = 20) (hxyz : ({x,y,z} : Finset α) ∈ F)
    (hxdeg : (F.filter (fun S => x ∈ S)).card = 6) :
    (F.filter (fun S => y ∈ S)).card ≤ 5 := by
  have hy := Erdos20RankThreeEven.rank_three_degree_le_six F hu hf y
  by_contra hnot
  have hydeg : (F.filter (fun S => y ∈ S)).card = 6 := by omega
  have h19 := card_le_nineteen_of_two_degree_six_vertices F x y z hu hf hxyz hxdeg hydeg
  omega

end Erdos20SharpTwenty
