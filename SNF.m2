preSmithNormalForm = method(
     Options => {
	  ChangeMatrix => {true, true},		    -- target, source
     	  KeepZeroes => true
	  }
     )
preSmithNormalForm Matrix := o -> (f) -> (
     if not isFreeModule source f or not isFreeModule target f then error "expected map between free modules";
     (tchg,schg,keepz) := (o.ChangeMatrix#0, o.ChangeMatrix#1,o.KeepZeroes);
     (tmat,smat) := (null,null);	-- null represents the identity, lazily
     (tzer,szer) := (null,null);	-- null represents zero, lazily
     R := ring f;
     R' := R[MonomialOrder => Position => Up];
     f' := promote(f,R');
     g := f';
     op := false;	       -- whether we are working on the transposed side
     count := 0;
     while true do (
	  flag := if op then tchg else schg;
	  G := gb(g, ChangeMatrix => flag, Syzygies => flag);
	  h := generators G;
	  if debugLevel > 100 then (
	       << "-- count = " << count << endl;
	       if op then (
		    << "-- lead terms in rows    (gb    ) : " << transpose leadTerm h << endl;
		    << "-- lead terms in columns (not gb) : " << leadTerm transpose h << endl;
		    )
	       else (
		    << "-- lead terms in columns (gb    ) : " << leadTerm h << endl;
		    << "-- lead terms in rows    (not gb) : " << transpose leadTerm transpose h << endl;
		    ));
     	  if count > 0 and h == g then break;	  
	  if op then (
	       if tchg then (
	       	    chg := getChangeMatrix G;
	       	    zer := mingens image syz G;
		    if keepz then (
			 if tmat === null
			 then (tmat,tzer) = (chg,zer)
			 else (tmat,tzer) = (tmat * chg, tmat * zer | tzer ))
		    else (
			 if tmat === null
			 then tmat = chg
			 else tmat = tmat * chg)))
	  else (
	       if schg then (
	       	    chg = getChangeMatrix G;
	       	    zer = mingens image syz G;
		    if keepz then (
			 if smat === null
			 then (smat, szer) = (chg, zer)
			 else (smat, szer) = (smat * chg, smat * zer | szer ))
		    else (
			 if smat === null
			 then smat = chg
			 else smat = smat * chg)));
	  g = transpose h;
	  op = not op;
	  count = count + 1;
	  print g;
	  print (tmat,tzer);
	  print (smat,szer);
	  );
     if op then g = transpose g;
     if tchg then (
	  if tmat === null
	  then tchange := id_(target f')
	  else (
     	       tmat = transpose tmat;
	       if keepz then (
     	       	    tzer = transpose tzer;
	       	    tchange = tmat || tzer;
	       	    g = g || map(target tzer, source g,0))
	       else tchange = tmat));
     if schg then (
	  if smat === null
	  then schange := id_(source f')
	  else (
	       if keepz then (
	       	    schange = smat | szer;
	       	    g = g | map(target g, source szer, 0))
	       else schange = smat));
     g = lift(g,R);
     -- D == P f Q ;
     D := map(R^(numgens target g),,g);			    -- this makes D homogeneous, if possible
     P := if tchg then map(target D,target f,lift(tchange,R));
     Q := if schg then map(source f, source D,lift(schange,R));
     ( D, P, Q ))

newSmithNormalForm = method()
newSmithNormalForm Matrix := f -> (
    --first run preSNF until done
    --sort diagonal entries
    --find 2 consecutive indices on diagonal missing divisibility criterion
    --do transformation on correct side, run preSNF again
    )
 end--------------------------------------

restart
load "smith-normal-mods.m2"

--example over QQ[x] that is broken
R = QQ[x]
h = transpose matrix{{x^3+1},{x^2+1}}
syz h

f = matrix{{3,-1,-1},{-1,3,-1},{-1,-1,3}}
preSmithNormalForm f

R = ZZ
D = matrix{
    {2,0,0},
    {0,0,0}
    }
P = random(R^2,R^2)
Q = random(R^3,R^3)
M = P*D*Q
(D',P',Q') = preSmithNormalForm M
P'*M*Q' == D'

---------
M = matrix{{4,0},{4,6}};
preSmithNormalForm M

preSmithNormalForm d

(D,P,Q) = preSmithNormalForm h
P*h*Q == D

smithNormalForm h
