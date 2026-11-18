#!/bin/bash
# NOTE (release 6.0): archived build script of the internal run; it refers to the project's internal directory layout and does not run in this repository. Kept for the record (commands, parameters).
# scan_closure.sh : import closure (Erdos634.* modules only) of AllV6h and AllV6 (+ all WGapB* sources): comment- and string-aware scan for
# sorry, native_decide, ofReduceBool, axiom (code position). Output: SCAN_RESULT.txt
ROOT=a scratch directory; R=$ROOT/internal working notes; L=$ROOT/lean
cd $L
roots="Erdos634.AllV6h Erdos634.AllV6 $(ls Erdos634/Draft | sed -n 's/^\(WGapB[0-9]*[cqFX][0-9]*\)\.lean$/Erdos634.Draft.\1/p' | tr '\n' ' ')"
find Erdos634 -name '*.lean' > $R/logs/_allfiles.txt
awk -v roots="$roots" '
 FNR==1 { f=FILENAME; m=f; sub(/\.lean$/,"",m); gsub("/",".",m); cur=m; file[m]=f }
 /^[ \t]*import[ \t]/ { for(i=2;i<=NF;i++) if($i ~ /^Erdos634\./) { n[cur]++; imp[cur, n[cur]]=$i } }
 END { nr=split(roots, rs, " "); q=0; for(i=1;i<=nr;i++){ if(!(rs[i] in seen)){seen[rs[i]]=1; qu[++q]=rs[i]} }
   for(h=1;h<=q;h++){ m=qu[h]; for(j=1;j<=n[m];j++){ d=imp[m,j]; if(!(d in seen)){seen[d]=1; qu[++q]=d} } }
   for(h=1;h<=q;h++) if(qu[h] in file) print file[qu[h]] }' $(cat $R/logs/_allfiles.txt) > $R/logs/_closure_files.txt
nf=$(grep -c . $R/logs/_closure_files.txt)
# comment/string-aware token scan
awk '
 FNR==1 { depth=0 }
 { line=$0; out=""; i=1; L=length(line)
   while(i<=L){ c=substr(line,i,1); c2=substr(line,i,2)
     if(depth>0){ if(c2=="/-"){depth++; i+=2} else if(c2=="-/"){depth--; i+=2} else i++; continue }
     if(c2=="/-"){depth=1; i+=2; continue}
     if(c2=="--"){break}
     if(c=="\""){ i++; while(i<=L){ d=substr(line,i,1); if(d=="\\"){i+=2; continue} if(d=="\""){i++; break} i++ } out=out " "; continue }
     out=out c; i++ }
   if(out ~ /(^|[^A-Za-z0-9_.])(sorry|sorryAx|native_decide|ofReduceBool|Lean\.ofReduceBool|axiom)([^A-Za-z0-9_]|$)/) print FILENAME ":" FNR ": " $0 }' $(cat $R/logs/_closure_files.txt) > $R/logs/_scan_hits.txt
nh=$(grep -c . $R/logs/_scan_hits.txt)
{ echo "SCAN $(date) closure files: $nf ; code-position hits (sorry|native_decide|ofReduceBool|axiom): $nh"; head -60 $R/logs/_scan_hits.txt; } > $R/SCAN_RESULT.txt
cat $R/SCAN_RESULT.txt | head -5
