import Erdos634.TP_erdos

namespace Erdos634.Draft.TP_erdosWrap
open Erdos634.TPErdos Erdos634.Geometry

theorem wrap_chain_edge_lengths_sum_witness :
    ∑ e ∈ wallDissection.lineChain wallF 0,
        ENNReal.ofReal (dist ((wallDissection.tile e.1).pts e.2)
          ((wallDissection.tile e.1).pts (e.2 + 1)))
      = ENNReal.ofReal (dist wallU wallV) :=
  chain_edge_lengths_sum_witness

example : True := trivial
#check @chain_edge_lengths_sum_witness

end Erdos634.Draft.TP_erdosWrap
