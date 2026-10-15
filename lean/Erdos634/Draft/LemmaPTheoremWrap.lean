import Erdos634.LemmaPTheorem
namespace Erdos634.Draft.LemmaPTheoremWrap
open Erdos634.LemmaPTheorem
open Erdos634.Geometry Erdos634.CertCoord Erdos634.CertNode Erdos634.LemmaPTree
  Erdos634.ThickBlockingLemmas

theorem wrap_lemmaP_no_dissection {N : ℕ} (D : CongruentDissection N)
    (htarget : D.target.carrier = target63.carrier)
    (hmodel : D.model.Congruent w1t0)
    (hbase : (∃ i, HasBaseEdge D.toDissection i 0 6) ∧ (∃ i, HasBaseEdge D.toDissection i 6 15) ∧
      (∃ i, HasBaseEdge D.toDissection i 15 20)) : False :=
  lemmaP_no_dissection D htarget hmodel hbase

theorem wrap_baseword_hyp_config :
    T0.carrier ⊆ TGT.carrier ∧ T1.carrier ⊆ TGT.carrier ∧ T5.carrier ⊆ TGT.carrier ∧
    Disjoint (interior T0.carrier) (interior T1.carrier) ∧
    Disjoint (interior T1.carrier) (interior T5.carrier) ∧
    Disjoint (interior T0.carrier) (interior T5.carrier) ∧
    T0.pts 0 = mkPt 0 0 ∧ T0.pts 1 = mkPt 6 0 ∧
    T1.pts 0 = mkPt 6 0 ∧ T1.pts 1 = mkPt 15 0 ∧
    T5.pts 0 = mkPt 15 0 ∧ T5.pts 1 = mkPt 20 0 :=
  baseword_hyp_config

theorem wrap_node2_jam_again {N : ℕ} (D : CongruentDissection N)
    (htarget : D.target.carrier = target63.carrier) (hmodel : D.model.Congruent w1t0)
    (hbase : (∃ i, HasBaseEdge D.toDissection i 0 6) ∧ (∃ i, HasBaseEdge D.toDissection i 6 15) ∧
      (∃ i, HasBaseEdge D.toDissection i 15 20))
    (i₀ i₁ : Fin N) (h₀ : D.tile i₀ = w1t0) (h₁ : D.tile i₁ = w1t1) : False :=
  node2_jam_again D htarget hmodel hbase i₀ i₁ h₀ h₁

example : True := trivial
#print axioms wrap_lemmaP_no_dissection
end Erdos634.Draft.LemmaPTheoremWrap
