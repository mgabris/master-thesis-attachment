# Backtrack complexity equations
Sage code for solving complexity estimate equations for state-recovery attacks on ciphers RC4 and Spritz.

File [compute.sage](./compute.sage) contains code for solving equations (with exception of Spritz special equations, where more elaborate way is needed) provided how to generate equations, variables used in them and their boundary conditions.

Files **_equations.sage* contain functions to generate equations, variables and boundary conditions for particular equation type. Each file contains brief code to compute complexities from equations.

There is also Sage worksheet file [equations.sws](./equations.sws) and jupyter notebook [equations.ipynb](./equations.ipynb) containing all above code.

Tradeoff experiments are in jupyter notebook [tradeoffs.ipynb](./tradeoffs.ipynb)

# Rovnice odhadov prehľadávania s návratom
Kód počítajúci rovnice odhadov v Sage.

Súbor [compute.sage](./compute.sage) obsahuje kód pre riešenie sústav rovníc (okrem rovníc pre špeciálny stav, keďže pre nich je potrebný komplikovanejší postup) za predpokladu, že mu poskytneme funkcie na vygenerovanie rovníc, premenných použitých v rovniciach a hraničných podmienok.

Súbory **_equations.sage* obsahujú funckie na vygenerovanie rovníc, premenných a hraničných podmienok pre konkrétny typ rovníc. Každý súbor obsahuje stručný kód počítajúci samotný odhad.

Nachádza sa tu tiež Sage worksheet súbor [equations.sws](./equations.sws) a jupyter notebook súbor [equations.ipynb](./equations.ipynb) obsahujúci všetok predošlý kód.

Tradeoff pre šifru Spritz a súvisiace experimenty sú v súbore [tradeoffs.ipynb](./tradeoffs.ipynb).
