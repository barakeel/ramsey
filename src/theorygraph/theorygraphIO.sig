signature theorygraphIO =
sig
  
  type thyid = string * Arbnum.num * Arbnum.num
  val thyid_of_thy : string -> thyid
  val theorygraph_of_thy : string -> (thyid * thyid list) list
  val write_theorygraph : string -> (thyid * thyid list) list -> unit
  val read_theorygraph : string -> (thyid * thyid list) list
  val write_theorygraph_of_thy : string -> unit
  val read_theorygraph_of_thy : string -> (thyid * thyid list) list
  
end
