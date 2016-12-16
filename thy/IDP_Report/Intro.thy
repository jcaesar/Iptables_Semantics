(*<*)
theory Intro
imports Prefix_Match
begin
(*>*)

chapter\<open>Introduction\<close>
section\<open>Background\<close>

text\<open>
Firewalls are core building blocks of state of the art information security systems.
Correctly configured firewalls can, e.g., isolate systems and prevent intrusions from easily spreading.
Unfortunately, firewall configuration is notoriously hard and mistakes are the rule and not the exception~\cite{wool2004quantitative}.
\<close>

text\<open>
One known cause for the many configuration errors in firewall configurations is the complexity of writing firewall rulesets.
The languages for writing firewall rulesets are often focused on low-level properties of single packets.
Expressing the high-level human view on traffic into these low-level expressions is error-prone.
\<close>

text\<open>
One particular aspect that increases the complexity is the multitude of ways that a high-level policy can be expressed.
For example, to match packets that are destined to the local interface, an operator might chose to match based on the output interface, \texttt{-o ethlocal}, or based on the destination IP address, \texttt{-d 131.159.14.0/25}.
Given an according configuration of the routing tables, the two ways are equal.
(The same does not necessarily hold true for input interfaces and source IP addresses.)
The complexity here stems from the (implicit) assumptions about the routing table.
These assumptions make it harder for a human to understand the intention of a firewall ruleset;
they also make automated analysis of firewall rulesets more complicated.
\<close>

text\<open>
An obvious example for this is generating (IP space) service matrices.
A match for a destination address can be done by either naming the address directly, or by naming the port to which the routing system would forward the packet.
\<close>

text\<open>
A different area where output port matches are difficult to deal with is when attempting to rewrite firewall matches to OpenFlow matches.
An OpenFlow match expression can, by purpose, not match on the output port, since it is used to decide the output port.
To translate a firewall match into an OpenFlow match, it is thus necessary to remove the match for the output port and replace it by something different.
\<close>

section\<open>This Work\<close>

text\<open>
presents an approach to solve both of these problems:
We rewrite the port matches of a firewall ruleset to matches on the IP addresses.
The main aspects of this work consider:
\begin{itemize}
\item under which conditions this can be done,
\item how the relevant background information can be obtained and processed,
\item how to do the actual rewriting,
\item under which conditions the rewriting retains the forwarding behavior of the ruleset.
\end{itemize}
The beauty of the rewriting approach lies in the fact that it can produce a new ruleset that is functionally equivalent and easier to analyze.
Thus, using rewriting does not require a single change to our existing frameworks and allows them to obtain more interesting results, or even to obtain results at all.
\<close>

text\<open>
To implement rewriting, this work formulates an updated notion of routing that is compatible with the context of~\cite{diekmann2015semantics}.
More concretely, this work integrates existing models of routing tables, and the model of the process of linux routing with the existing formalization of iptables firewalls.
This includes allowing for transformations of firewall rulesets in that context.
The subtasks required for this are listed following.
\begin{itemize}
	\item Formulate a rewriting procedure for output ports to destination addresses that draws upon the routing tables.
	\item Formalize the reverse path filtering style spoofing protection.
	\item Formulate a rewriting procedure for input ports to source addresses, under the assumption of a separate spoofing protection. Prove the procedure correct.
\end{itemize}
\<close>

text\<open>
Since the rewriting strengthens our frameworks, we also re-evaluated our existing datasets.
This work contains the following re-evaluations.
\begin{itemize}
	\item Re-evaluate our existing datasets with the ``refined'' service mask calculation.
	\item Evaluate an existing translation system of Linux firewall configuration to OpenFlow tables on real-world data.
\end{itemize}
\<close>

section\<open>Isabelle/HOL\<close>
text\<open>
This work is based on and done in Isabelle/HOL~\cite{isabellehol}, an \emph{LCF\footnote{Logic for Computable Functions} style} theorem prover.
Isabelle is a system for implementing formalisms, and Higher Order Logic (HOL), is a system for functional programming and logic.
Together, they form a generic theorem prover\footnote{Occasionally, the term \emph{Isabelle} is used as \emph{pars pro toto} for \emph{Isabelle/HOL} and adjuncts like \emph{Isabelle/jEdit}}.
Isabelle/HOL's purpose is not to find entirely new theorems on its own, but to allow to check proofs that have been given by humans with a high reliability.
This is ensured by the fact that all proofs that are accepted by Isabelle have to pass its inference kernel, a small part of the program that has been developed and analyzed with care by many experts of the formal methods community.
In the 20 years of Isabelle's development, of the few unsoundness problems that have been discovered in Isabelle, not a single one was found in production.
In general, facts that have been proved with Isabelle/HOL can be accepted as well-founded truth.
\<close>

text\<open>
This document has been generated using Isabelle/HOL, allowing to directly show the original theorems and lemmas as they are stated and proved.
The definitions, lemmas and theorems stated here are merely repetitions of facts state in other theory files.
This allows us to present the important things in a brief manner while ellipsizing the plethora of necessary auxiliary definitions and helper lemmas.
Additionally, this form makes it impossible to intentionally hide any assumptions and prevents any involuntary errors when transferring the theorems from Isabelle/HOL to \LaTeX{}.
Unfortunately, the technique also has two downsides:
The reader is left with some of the idiosyncrasies of Isabelle notation, 
  and it additionally introduces some notational inaccuracies, 
  e.g. what was originally a definition is presented as a lemma or schematic goal here.
\<close>

text\<open>
A short overview over the Isabelle/HOL notation follows:
\begin{itemize}
	\item Type variables are denoted as @{typ "'a"}.
	\item Derived types are denoted from right-to-left, e.g. @{typ "nat list"} is a list of natural numbers, @{typ "('a :: len) word"} is a word of length @{typ "'a"}.
	\item The machine word types are used for IP addresses; @{typ "32 word"} is used for IPv4 addresses, @{typ "128 word"} for IPv6 addresses.
	\item The (product) type of a touple with members @{typ "'a"} and @{typ "'b"} is denoted as @{typ "'a \<times> 'b"}.
	\item A tuple of @{term a} and @{term b} is denoted as @{term "(a,b)"}
	\item Lists (e.g. @{term "[a,b,c]"}) are constructed using @{term "op #"} and concatenated using @{term "op @"}, e.g. @{term "s @ a # t"}.
	\item \todo{}
\end{itemize}
\<close>

text\<open>
Since Isabelle/HOL, just like any other software, receives regular updates and changes over time, it can happen that theory files and proofs that once worked will not do so with future versions of Isabelle/HOL.
This can be because the names of the lemmas that were used in the proofs change and thus can't be found anymore,
	because a prover that is being used happens to apply inequalities in a different order and thus produces an unsolvable goal, 
	or because new definitions were introduced changed the meaning of lemmas.
(This happened in Isabelle 2016-1, where the identifiers @{term pi} and @{term ii} were introduced as real constants. 
	The lemmas that used the string @{term ii} as a free variable and abbreviation for \emph{input interface} consequently stopped working.)
To save proofs from this kind of bit-rot, the Isabelle maintainers maintain the \emph{Archive of Formal Proof (AFP)}, a journal of Isabelle proofs, together with Isabelle.
This ensures that interesting theory will be available to future authors, even if the surrounding scientific community loses interest for a while and the original authors have dedicated their time to other projects.
All theorems that we present here, and their proofs, have been published to the AFP and should thus continue to work and be extensible and usable with Isabelle/HOL for a long time~\cite{IP_Addresses-AFP,Simple_Firewall-AFP,Routing-AFP,Iptables_Semantics-AFP,LOFT-AFP}.
\<close>

(*<*)
end
(*>*)