(*<*)
theory EvalLOFT
imports Main "../LOFT/Examples/SQRL/SQRL_Router"
begin
(*>*)

section\<open>Re-evaluation of LOFT\<close>
text_raw\<open>\label{sec:evalloft}\<close>
text\<open>This section will re-evaluate the results of LOFT~\cite{LOFT-AFP} based on real-world data.
This section assumes basic familiarity with LOFT.
If any details of the explanations are unclear, please refer to the original publication~\cite{LOFT-AFP}.
As a short remainder: LOFT transforms a routing table and a firewall from a Linux device
into two lists of pairs, each pair containing a @{type simple_match} and an action
(either a port to forward to, or one of @{term "{Accept,Drop}"}).
We call this format of a list of pair of match expression and an action of arbitrary type a
generalized (simple) firewall.
The idea is that, in a Linux style router, these two generalized firewalls are considered sequentially
for a routing/forwarding decision.
With that model, we can execute the process shown in Figure~\ref{fig:loft}:
If we form the cross product of these two firewalls and conjoin the match expression ($\bowtie$),
we can obtain a single generalized firewalls that computes the same decision in one step.
This single generalized firewalls can easily be converted to an OpenFlow table, with one catch:
the match expressions can match on an output port,
but such a match does not make sense in an OpenFlow table.
Hence, we had to require that the input firewall does not contain output interface matches.
This very fact was another motivation for this work:
if we have output interface rewriting, we can just remove output interface matching without
loosing any information that would be relevant for the forwarding behavior.
We finally wanted to put this to a test on a real-world configuration.
For this purpose, we will reuse the configuration from Section~\ref{sec:sqrlfweval}.
\<close>
text_raw\<open>
\tikzset{
    iop/.style={draw,diamond,aspect=2},
    tran/.style={draw,rounded corners=2mm},
    act/.style={draw,circle},
}
\begin{figure}
\centering
\scalebox{0.666}{
\begin{tikzpicture}[node distance=2cm]
    \node [iop] (rt) at (0,0) {\texttt{ip route}};
    \node [iop] (fw) at (4cm,0) {simple firewall};
    \node [tran] (grt) at (0,-1.5cm) {$\left[\left(\mathrm{match} \times \mathrm{oiface}\right)\right]$};
    \draw [->] (rt) -- (grt);
    \node [act] (j) at (2cm,-2.5cm) {$\bowtie$};
    \draw [->] (grt) -- (j);
    \coordinate (gfw) at (4cm,-1.5cm);
    \draw [->] (fw) -- (gfw) -- (j);
    \node [tran] (of) at (2cm,-3.6cm) {OpenFlow};
    \draw [->] (j) -- (of);
    \node [iop] (ofo) at (2cm,-5.0cm) {single table};
    \draw [->] (of) -- (ofo);
\end{tikzpicture}
}
\caption{LOFT rewriting: quick overview}
\label{fig:loft}
\end{figure}
\<close>
text\<open>
However, there is still one problem: the firewall in question uses stateful matches.
When analyzing firewalls in Section~\ref{sec:evalm}, we looked at the behavior for packets that
belong to new connections.
If we build a configuration for a stateful device that only forwards packets as if they were new,
much of the original functionality will likely be lost.
On the other hand, if we permit all packets as if they are in the established state,
we will likely allow too much%
\footnote{We could even compute a firewall that accepts packets if the original firewall would have
accepted them in either one state.
But since configurations tend to accept all established packets if they accept the corresponding new packets,
there is no point in doing so.}.
Given that many firewall configurations start with accepting all packets in established connections,
the resulting configuration will simply forward all packets.
\<close>
text_raw\<open>
\begin{figure}
\begin{verbatim}
			table=0,priority=2,arp,action=flood
			table=0,priority=2,ipv4,ct_state=-trk,action=ct(table=1,zone=42)
			table=0,priority=2,ipv6,action=drop
			table=0,priority=1,action=drop

			table=1,priority=2,ip,ct_state=+trk+new,action=goto_table:2
			table=1,priority=2,ip,ct_state=+trk+est,action=goto_table:3
			table=1,priority=1,action=drop
\end{verbatim}
\caption{OVS rules for separating packets into tables based on state}
\label{fig:ovsconntrack}
\end{figure}
\<close>
text\<open>Our solution for this problem is to take a step back:
In this case, we want to experimentally verify a concrete IPv4 only \todo{mention that upstream} configuration transformation
 using Mininet~\cite{mininet} and OpenVSwitch (OVS) \cite{openvswitch}.
Instead of clinging to our pure formalization abiding by the OpenFlow~\cite{specification10} standard,
we recombine our results freely.
OpenVSwitch features the capability to hand packets to the Linux \texttt{conntrack} module
and do stateful matches.
With the set of rules shown in Figure~\ref{fig:ovsconntrack}%
\footnote{The configuration floods ARP requests because the generated tables will only forward IP traffic.}%
$^{\text{,}}$%
\footnote{Since the original device was IPv4 only, we drop IPv6.
We should, in theory, be able to generate two more OpenFlow tables to handle IPv6.}
, it is possible to separate packets
into different tables.
Hence, we simply use our tools to generate two, not one, OpenFlow table, 
one for new and one for established connections and load these into the appropriate tables.
The only thing that is left to do is to slightly modify the ruleset for the table
for new connections: if a packet is accepted and forwarded, update the \texttt{conntrack} state,
i.e. all rules with an action \texttt{output} get an additional action \texttt{ct(commit,zone=42)}.
An overview over this process is shown in Figure~\ref{fig:loftext}.
\<close>
text_raw\<open>
\begin{figure}
\centering
  \scalebox{0.6}{
\begin{tikzpicture}[node distance=1cm]
	\node[iop] (fw) {\texttt{iptables-save}};
	\node[tran,below of=fw,node distance=1.5cm] (par) {parse};
	\draw[->] (fw) -- (par);
	\node[tran,below of=par] (uf) {unfold};
	\draw[->] (par) -- (uf);
	\node[act,below of=uf] (uc1) {$\bigsqcap$};
	\draw[->] (uf) -- (uc1);
	\node[tran] (new) at (-4cm,-4.5cm){assume new};
	\draw[->] (uc1) -- (new);
	\node[act,below of=new] (uc3) {$\bigsqcap$};
	\draw[->] (new) -- (uc3);
	\node[tran,below of=uc3] (orw) {$\mathrm{oiface}$ rewrite};
	\node[tran] (rr) at (-1cm,-5.5cm) {routing relation};
	\node[iop] (ipr) at (-4cm,0) {\texttt{ip route}};
	\draw[->] (uc3) -- (orw);
	\draw[->] (ipr) -- (rr) -- (orw);
	\node[act,below of=orw] (uc2) {$\bigsqcap$};
	\draw[->] (orw) -- (uc2);
	\node[tran,below of=uc2] (irw) {$\mathrm{iiface}$ rewrite};
	\coordinate[right of=irw] (assmt) at (0,-7cm);
	\node[iop] (ipa) at (4cm,0) {IP assmt};
	\draw[->] (uc2) -- (irw);
	\draw[->] (ipa) -- (assmt) -- (irw);
	\node[act,below of=irw] (uc4) {$\bigsqcap$};
	\draw[->] (irw) -- (uc4);
	\node[tran,below of=uc4] (sfwt) {simple firewall};
	\draw[->] (uc4) -- (sfwt);

	\node[tran] (new-est) at (4cm,-4.5cm){assume established};
	\draw[->] (uc1) -- (new-est);
	\node[act,below of=new-est] (uc3-est) {$\bigsqcap$};
	\draw[->] (new-est) -- (uc3-est);
	\node[tran,below of=uc3-est] (orw-est) {$\mathrm{oiface}$ rewrite};
	\draw[->] (uc3-est) -- (orw-est);
	\draw[->] (rr) -- (orw-est);
	\node[act,below of=orw-est] (uc2-est) {$\bigsqcap$};
	\draw[->] (orw-est) -- (uc2-est);
	\node[tran,below of=uc2-est] (irw-est) {$\mathrm{iiface}$ rewrite};
	\draw[->] (uc2-est) -- (irw-est);
	\draw[->] (assmt) -- (irw-est);
	\node[act,below of=irw-est] (uc4-est) {$\bigsqcap$};
	\draw[->] (irw-est) -- (uc4-est);
	\node[tran,below of=uc4-est] (sfwt-est) {simple firewall};
	\draw[->] (uc4-est) -- (sfwt-est);

	\node [tran] (grt) at (0,-11.5cm) {$\left[\left(\mathrm{match} \times \mathrm{oiface}\right)\right]$};
	\coordinate (a) at ($(ipr)!0.22!(grt)$) {};
	\coordinate (b) at ($(ipr)!0.3!(grt)$) {};
	\coordinate (c) at ($(ipr)!0.73!(grt)$) {};
	\coordinate (d) at ($(ipr)!0.78!(grt)$) {};
	\draw [->] (ipr) -- (a) (d) -- (grt);
	\draw [dashed] (a) -- (b) (c) -- (d);

\begin{scope}[name=lofte,shift={(0,-10cm)}]
    \node [act] (j-est) at (2cm,-2.5cm) {$\bowtie$};
    \draw [->] (grt) -- (j-est);
	\coordinate (gfw-est) at (4cm,-1.5cm);
    \draw [->] (sfwt-est) -- (gfw-est) -- (j-est);
    \node [tran] (of-est) at (2cm,-3.6cm) {OpenFlow};
    \draw [->] (j-est) -- (of-est);
\end{scope}

\begin{scope}[name=loftn,shift={(-8cm,-10cm)}]
    \node [act] (j-new) at (6cm,-2.5cm) {$\bowtie$};
    \draw [->] (grt) -- (j-new);
	\coordinate (gfw-new) at (4cm,-1.5cm);
    \draw [->] (sfwt) -- (gfw-new) -- (j-new);
    \node [tran] (of-new) at (6cm,-3.6cm) {OpenFlow};
    \draw [->] (j-new) -- (of-new);
\end{scope}

	\coordinate [below of=of-new,node distance=0.7cm] (ofnc);
	\coordinate [below of=of-est,node distance=0.7cm] (ofec);
	\node[tran] (fin) at (0,-15cm) {OVS magic};
	\draw[->] (of-new) -- (ofnc) -- (fin);
	\draw[->] (of-est) -- (ofec) -- (fin);

	\node[iop,below of=fin,node distance=1.8cm] (cfg) {OVS config};
	\draw[->] (fin) -- (cfg);


\end{tikzpicture}
}
\caption{Full rewriting process used}
The nodes labeled $\bigsqcap$ signify use of the @{const upper_closure} function.
\label{fig:loftext}
\end{figure}
\begin{figure}
\scalebox{0.9}{
\begin{minipage}{\textwidth}
\tiny
@{thm[break] (rhs) SQRL_fw_simple_new_openflow_14} \\
$\ldots$
\end{minipage}
}
\caption{Start of generated OpenFlow table for new packets}
\label{fig:ovsgenerated}
\end{figure}
\<close>
text\<open>As an example, the first fourteen rules of the table for new packets as originally produced by LOFT
 are shown in Figure~\ref{fig:ovsgenerated}.
We have written a script to load both,
the original configuration and the translated OVS configuration into a Mininet environment.
The script also creates one directly attached host per attached interface%
\footnote{We have tested indirectly attached hosts / hosts reachable through another router
in the original LOFT evaluation and did not feel the need to re-evaluate that.}
and we tested reachability, again on TCP port 80%
\footnote{We also tested port 139 and ICMP ping, but the results did not differ},
for all pairs of hosts%
\footnote{Reachability to the device itself is not preserved and we did not test it.}.
The result is shown in Table~\ref{tab:sqrlaccmat}.
The networks (indicated by their interfaces names) are ordered from left to right,
by descending number of other interfaces they can be accessed from.
As can be seen, the original configuration and the OVS ruleset from the conversion behave identically
in all tested cases.
Great success!
\<close>
text_raw\<open>
\begin{table}
\begin{minipage}{0.6\textwidth}
\begin{tabular}{lccccccccc}
 \hspace{2ex} $\Rsh$ &
 \rotatebox{90}{\texttt{lup}  } &
 \rotatebox{90}{\texttt{vshit}} &
 \rotatebox{90}{\texttt{ldit} } &
 \rotatebox{90}{\texttt{lmd}  } &
 \rotatebox{90}{\texttt{loben}} &
 \rotatebox{90}{\texttt{wt}   } &
 \rotatebox{90}{\texttt{wg}   } &
 \rotatebox{90}{\texttt{vocb} } &
 \rotatebox{90}{\texttt{vpriv}} \\
\texttt{lup}   &   & ▭ & ▭ & ▭ & ▭ & ▭ & ▭ & ▭ & ▭\\ 
\texttt{vshit} & ■ &   & ▭ & ▭ & ▭ & ▭ & ▭ & ▭ & ▭\\ 
\texttt{ldit}  & ■ & ■ &   & ■ & ■ & ■ & ▭ & ▭ & ▭\\ 
\texttt{lmd}   & ■ & ■ & ■ &   & ■ & ■ & ▭ & ▭ & ▭\\ 
\texttt{loben} & ■ & ■ & ■ & ■ &   & ■ & ▭ & ▭ & ▭\\ 
\texttt{wt}    & ■ & ■ & ■ & ■ & ■ &   & ▭ & ▭ & ▭\\ 
\texttt{wg}    & ■ & ▭ & ▭ & ▭ & ▭ & ▭ &   & ▭ & ▭\\ 
\texttt{vocb}  & ▭ & ▭ & ▭ & ▭ & ▭ & ▭ & ▭ &   & ▭\\ 
\texttt{vpriv} & ▭ & ▭ & ▭ & ▭ & ▭ & ▭ & ▭ & ▭ &  \\ 
\end{tabular}
\end{minipage}
\begin{minipage}{0.39\textwidth}
Legend:\\
\begin{tabular}{lc}
no access & ▭ \\
access only with Linux router & ◩ \\
access only with OVS & ◪ \\
access with both & ■
% makes a lot of sense when opened in isabelle/jedit? well, utf-8, why would you support it.
% (I mean. srsly.)
\end{tabular}
\end{minipage}
\caption{Access matrix for original and converted configuration}
\label{tab:sqrlaccmat}
\end{table}
\<close>
  

(*<*)
end
(*>*)
