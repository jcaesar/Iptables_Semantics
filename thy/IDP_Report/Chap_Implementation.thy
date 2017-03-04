(*<*)
theory Chap_Implementation
imports Main
begin
(*>*)

chapter\<open>Implementation\<close>
section\<open>Overview\<close>
text\<open>The sections of this chapter describe the different aspects of the implementation and present the most important theorems on them.\<close>

text\<open>The sections are presented in the topological order of the dependencies of the underlying theory code.
We chose this order because it allows us to only introduce a definition when we have introduced all the things it is based on.
Unfortunately, this means that it cannot always be clear why a definition has been made in a certain way,
as the purpose of its details are often only revealed upon use.
\<close>
text\<open>Section \ref{sec:routing} shows a formalization of routing tables 
and documents tools for analyzing and transforming routing tables.\<close>
text\<open>Based upon that, \ref{sec:rpf} shows a formalization of Reverse Path Filtering.
The main results presented there are a hierarchy of the different reverse path filtering types and a 
transformation of routing tables to interface-IP relations for reverse path filtering.\<close>
text\<open>The goal of sections \ref{sec:routing} and \ref{sec:rpf} is to produce a relations that describes 
the connection between interfaces and what set of IP addresses are allowed or expected to appear on these interfaces.\<close>
text\<open>Based upon the results of those sections and \cite{diekmann2016verified}, Section \ref{sec:irew} shows a method to refine the analysis of firewall rulesets
by transforming interface matches to matches on IP addresses.\<close>


(*<*)
end
(*>*)
