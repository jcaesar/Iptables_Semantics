# shebang not possible… launch it as sed -nur -f

/=========== .* port .*->.* =========/ {
	s/^=+ (.*) port (.*)->(.*) =+/digraph \1_\2_\3 {/p;
	:node;
	# d |-> {10.13.41.0 .. 10.13.41.15} u {10.13.43.0 .. 10.13.43.15}
	n;
	/\|->/ {
		h;
		:un1; s/(\|->.*)u /\1  \\n∪ /; t un1;
		s/\.\./…/g;
		s/^(.*) \|-> (.*)(\\n)?$/\1 [label="\2" /;
		x;
		s/$/ /;
		s/\{/$\\left\\{/g;
		s/\}/\\right\\}$/g;
		s/(([0-9]+\.){3}[0-9]+) \.\. (([0-9]+\.){3}[0-9]+)/\\mathrm{\\texttt{\1}} \\ldots \\mathrm{\\texttt{\3}}/g;
		s/([^{])(([0-9]+\.){3}[0-9]+)([^}])/\1\\texttt{\2}\4/g;
		:un2; s/(\|->.*) u /\1 \\\\ $~\\cup~$ /; t un2;
		s/^.* \|-> (.*)(\\n)?$/ texlbl="\1"];/;
		x;G;
		s/\n//g;
		p;
		b node;
	};

	:edge;
	# (d,b)
	n;
	s/\((.*),(.*)\)/\1 -> \2;/p;
	t edge;
	# this depends on the fact that there's an empty line before the next graph.
	s/^.*$/}\n/p;
}


