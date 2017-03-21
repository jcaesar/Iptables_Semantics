function d2t { dot2tex --figonly --graphstyle='scale=.4, every node/.style={scale=.56,align=center}' --usepdflatex $@; };   
	
../../../../haskell_tool/dist/build/fffuu/fffuu --service_matrix_dport 80 --ipassmt ipassmt_sqrl_new --routingtbl ip-route iptables-save |  sed -nur -f ../../../../haskell_tool/tograph.sed | dot -Txdot |  sed -n '/label/{:a;/\\$/{n;b a;};s/^.*$/_ldraw_="F 14 11 -Times-Roman c 7 -#000000 T 552.39 157.42 0 148 29"/;};p' |  d2t --preproc | d2t >../../../IDP_Report/document/figures/sqrl_rtr_full.tex 

function d2t { dot2tex --figonly --graphstyle='scale=.5, every node/.style={scale=.7,align=center}' --usepdflatex $@; };   

../../../../haskell_tool/dist/build/fffuu/fffuu --service_matrix_dport 80 iptables-save |  sed -nur -f ../../../../haskell_tool/tograph.sed | dot -Txdot |  sed -n '/label/{:a;/\\$/{n;b a;};s/^.*$/_ldraw_="F 14 11 -Times-Roman c 7 -#000000 T 552.39 157.42 0 148 29"/;};p' |  d2t --preproc | d2t >../../../IDP_Report/document/figures/sqrl_rtr_none.tex 

	
../../../../haskell_tool/dist/build/fffuu/fffuu --service_matrix_dport 80 --ipassmt ipassmt_sqrl_new iptables-save |  sed -nur -f ../../../../haskell_tool/tograph.sed | dot -Txdot |  sed -n '/label/{:a;/\\$/{n;b a;};s/^.*$/_ldraw_="F 14 11 -Times-Roman c 7 -#000000 T 552.39 157.42 0 148 29"/;};p' |  d2t --preproc | d2t >../../../IDP_Report/document/figures/sqrl_rtr_assmt.tex 

../../../../haskell_tool/dist/build/fffuu/fffuu --service_matrix_dport 80 --routingtbl ip-route iptables-save |  sed -nur -f ../../../../haskell_tool/tograph.sed | dot -Txdot |  sed -n '/label/{:a;/\\$/{n;b a;};s/^.*$/_ldraw_="F 14 11 -Times-Roman c 7 -#000000 T 552.39 157.42 0 148 29"/;};p' |  d2t --preproc | d2t >../../../IDP_Report/document/figures/sqrl_rtr_rtbl.tex 

