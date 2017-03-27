(*<*)
theory ChapSema
imports "../Iptables_Semantics/Alternative_Semantics"
begin
  
notation (Axiom output)
  "Trueprop"  ("\<^latex>\<open>\\mbox{}\\inferrule{\\mbox{}}{\\mbox{\<close>_\<^latex>\<open>}}\<close>")

notation (Rule output)
  Pure.imp  ("\<^latex>\<open>\\mbox{}\\inferrule{\\mbox{\<close>_\<^latex>\<open>}}\<close>\<^latex>\<open>{\\mbox{\<close>_\<^latex>\<open>}}\<close>")

syntax (Rule output)
  "_bigimpl" :: "asms \<Rightarrow> prop \<Rightarrow> prop"
  ("\<^latex>\<open>\\mbox{}\\inferrule{\<close>_\<^latex>\<open>}\<close>\<^latex>\<open>{\\mbox{\<close>_\<^latex>\<open>}}\<close>")

  "_asms" :: "prop \<Rightarrow> asms \<Rightarrow> asms" 
  ("\<^latex>\<open>\\mbox{\<close>_\<^latex>\<open>}\\\\\<close>/ _")

  "_asm" :: "prop \<Rightarrow> asms" ("\<^latex>\<open>\\mbox{\<close>_\<^latex>\<open>}\<close>")

term "Decision FinalAllow"

abbreviation "state_allow_pr \<equiv> Decision FinalAllow"
notation (latex) "state_allow_pr" ("\<^latex>\<open>\\ensuremath{\\textnormal{\\circled{\\small \\Checkmark}}}\<close>")
abbreviation "state_deny_pr \<equiv> Decision FinalDeny"
notation (latex) "state_deny_pr" ("\<^latex>\<open>\\ensuremath{\\textnormal{\\circled{\\small \\XSolidBrush}}}\<close>")
abbreviation "state_undecided_pr \<equiv> Undecided"
notation (latex) "state_undecided_pr" ("\<^latex>\<open>\\ensuremath{\\textnormal{\\circled{\\textnormal{\\large \\textbf{?}}}}}\<close>")
  
(*datatype action = Accept | Drop | Log | Reject | Call string | Return | Goto string | Empty | Unknown*)
notation (latex) Accept ("\<^latex>\<open>\\textnormal{\\texttt{Accept}}\<close>")
notation (latex) Drop ("\<^latex>\<open>\\textnormal{\\texttt{Drop}}\<close>")
notation (latex) Log ("\<^latex>\<open>\\textnormal{\\texttt{Log}}\<close>")
notation (latex) Reject ("\<^latex>\<open>\\textnormal{\\texttt{Reject}}\<close>")
notation (latex) Call ("\<^latex>\<open>\\textnormal{\\texttt{Call}}\<close>")
notation (latex) Return ("\<^latex>\<open>\\textnormal{\\texttt{Return}}\<close>")
notation (latex) Empty ("\<^latex>\<open>\\textnormal{\\texttt{Empty}}\<close>")
notation (latex) Rule ("'(_, _')")

lemma call_result':  "\<lbrakk> matches \<gamma> m p; \<Gamma> c = Some rs; \<Gamma>,\<gamma>,p\<turnstile> rs \<Rightarrow>\<^sub>r t; 
  t \<in> {Decision FinalAllow, Decision FinalDeny} \<rbrakk> \<Longrightarrow>
               \<Gamma>,\<gamma>,p\<turnstile> Rule m (Call c) # rrs \<Rightarrow>\<^sub>r t"
  by(auto simp add: iptables_bigstep_r.call_result)
    
lemma fin_ran_alt: "finite (ran \<Gamma>) = finite {rs. \<exists>c. \<Gamma> c = Some rs}" unfolding ran_def by simp
  
    
  
(*>*)
chapter\<open>Model Re-evaluation\<close>
text\<open>\todo{Introduce this chapter in a content overview, if I have one}
Many of the theorems that assure the correctness of things we claimed in Chapter~\ref{chap:implementation}
are based on the assumption that the semantics we published in 
\cite{diekmann2015semantics,Iptables_Semantics-AFP} correctly represents the behavior of iptables.
While we have invested a large amount of time into manually checking those rules and
also proved a number of theorems that ensure basic correctness properties of the semantics,
like termination (under a wellformedness criterion) or determinism,
we wanted to further improve the confidence in and understanding of our semantics.
To do so, we defined in a second semantics with a substantially different format.
The idea is that it is rather unlikely that the same hard-to-spot bug hides in two different formulations
of the same facts.
\<close>
text_raw\<open>
\begin{figure}
\centering
\small % explain smollness - am pupper
\onehalfspacing
@{thm [mode=Axiom] skip[no_vars]}~{\sc Skip} \hspace{4ex}
@{thm [mode=Rule] accept[no_vars]}~{\sc Accept} \hspace{4ex}
@{thm [mode=Rule] drop[no_vars]}~{\sc Drop} \hspace{4ex}
@{thm [mode=Rule] reject[no_vars]}~{\sc Reject} \hspace{4ex}
@{thm [mode=Rule] return[no_vars]}~{\sc Return} \hspace{4ex}
@{thm [mode=Rule] log[no_vars]}~{\sc Log} \hspace{4ex}
@{thm [mode=Rule] empty[no_vars]}~{\sc Empty} \hspace{4ex}
@{thm [mode=Rule] nms[no_vars]}~{\sc NoMatch} \hspace{4ex}
@{thm [mode=Rule] call_result'[no_vars]}~{\sc CallResult} \hspace{4ex}
@{thm [mode=Rule] call_no_result[where chain=c,no_vars]}~{\sc CallNoResult} \hspace{4ex}
\caption{Rules of the alternative iptables semantics}
\label{fig:altrules}
\end{figure}
\<close>
text\<open>We show the rules of the alternative formulation in Figure~\ref{fig:altrules}.
The rules of the original semantics can be taken from \cite{Iptables_Semantics-AFP} (but the typesetting here follows tye style from \cite{diekmann2015semantics}).
The main motivation for this reformulation was the format of the \textsc{CallReturn} rule.
We wanted a semantics that allows \texttt{Call} on the top level.
Given that we wanted to keep the three possible states, @{term Undecided}, @{term "Decision FinalAllow"}
and @{term "Decision FinalDeny"}, it is not possible to introduce a rule like \textsc{Return}
while keeping the \textsc{Seq} rule.
Hence, the first refinement step towards the alternative semantics is to remove the \textsc{Seq}
and \textsc{Decision} rules and replace their functionality by
\begin{itemize}
  \item allowing rules that make a decision to discard all rules following them, and by 
  \item letting rules that do not make a decision ``retrieve'' their decision from the rules that follow them.
\end{itemize}
This immediately required introducing a rule similar to \textsc{CallNoResult}.
In a second refinement step, we removed the initial state since now all rules assumed an initial state of @{term Undecided}.
In a third refinement step, we introduced the \textsc{Return} rule shown here and removed the \textsc{CallReturn} rule.
\<close>
text\<open>We have formulated different versions of theorems showing the equality of the two semantics,
 the most refined being:\<close>
corollary "\<lbrakk>finite (ran \<Gamma>); \<forall>r \<in> set rs. get_action r \<noteq> Return\<rbrakk> \<Longrightarrow>
  \<Gamma>,\<gamma>,p\<turnstile> rs \<Rightarrow>\<^sub>r t \<longleftrightarrow> \<Gamma>,\<gamma>,p\<turnstile> \<langle>rs, Undecided\<rangle> \<Rightarrow> t" by (fact r_eq_orig''')
text\<open>Assuming that none of the rules in \<open>rs\<close> is @{const Return} is obviously necessary due to the format of the
\textsc{CallReturn} rule:
the original semantics cannot make progress if there is a matching @{const Return} in the topmost chain%
\footnote{As such, the assumption is only needed for one direction of the equality and slightly too strong.
We nevertheless think that this is the sane way of making this assumption.}.
The assumption @{thm (lhs) fin_ran_alt[no_vars]}, i.e. @{thm (rhs) fin_ran_alt[no_vars]} is necessary for the induction
for the inductive proof of the third refinement step from left to right: if \<open>\<Gamma>\<close> only contains finitely many chains,
then we can always find a name \<open>c\<close> for a chain that is not being called from any chain.
With that, we can update @{term "\<Gamma>(c \<mapsto> rs)"}  and wrap \<open>rs\<close> in a @{term "[Rule MatchAny (Call c)]"} 
to be able to simulate \textsc{Return} with \textsc{CallReturn}.
The fact that \<open>c\<close> is not being called from any chain is necessary so we can freely modify
what \<open>rs\<close> \<open>c\<close> is being updated to in the induction.
The proof follows somewhat laboriously.
\<close>
text\<open>
This gives us the desired heigthened confidence in our semantics.
An additional ``side effect'' of the alternative semantics is that it would be much easier to define a rule for \texttt{Goto}.
However, since the alternative semantics is harder to work in than our main semantics
(for the lack of a \textsc{Seq} rule), we do not see much to gain in doing so.
\<close>
(*<*)
end
(*>*)
