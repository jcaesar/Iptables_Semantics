(*<*)
theory InterfaceRewriting
imports Main
begin
(*>*)

section\<open>Interface Rewriting\<close>
text_raw\<open>\label{sec:irew}\<close>

(*

Read the routing table
produce a relation ip-interval -> port (position independent, reduced intervals)
invert the relation
(proof: strict rpf (RCF3704) corresponds to this)
transform to ipassmt (split intervals)

Fundamental difference: output port rewriting should kill anything that is not in the routing table. when generating the assignment naively, interfaces with no routing rule receive no entry in the ipassignment. the interface rewriting will ignore interfaces with no entry, and they will later be abstracted to match all, yielding overapproximation.
*)

(*<*)
end
(*>*)
