signature genb =
sig

  type mat = int Array2.array

  val sample_number : int ref
  val max_hole : int ref
  val greedy_cover : IntInf.int Redblackset.set -> (mat * (int * int) list) list
  
  
end
