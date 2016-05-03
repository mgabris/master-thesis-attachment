# Tool for generating random states of ciphers RC4 and Spritz
Random states are generated with script [generate.py](./generate.py), all options can be printed invoking this script with switch ```-h```.

Special state is availible only for Spritz.

To generate states in format for [SMT tool](../smt), use switch ```--smt```. Revealing values or setting prefix length have no effect with this option, as only fully revealed state is used in SMT tool.

# Nástroj na generovanie náhodných stavov šifier RC4 a Spritz
Náhodné stavy sú generované skriptom [generate.py](./generate.py), všetky možnosti nastavení sa vypíšu pomocu prepínača ```-h```.

Generovanie špeciálnych stavov je možné iba pre šifru Spritz.

Pre vygenerovanie stavov vo formáte pre [SMT nástroj](../smt) treba použiť prepínač ```--smt```. Nastavenia pre prednastavenie hodnôt v stave a prefix bežiaceho kľúča s prepínačom ```--smt``` nemajú žiadny efekt, tieto informácie SMT nástroj nepoužije.
