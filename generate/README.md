# Generating random states
Script [generate.py](./generate.py) generates random states for ciphers RC4 and Spritz.

All options can be printed invoking this script with switch ```-h```.

Special state is availible only for Spritz.

To generate states in format for [SMT tool](../smt), use switch ```--smt```. Revealing values or setting prefix length have no effect with this option, as only fully revealed state is used in SMT tool.

# Generovanie náhodných stavov
Skript [generate.py](./generate.py) generuje náhodné stavy šifier RC4 a Spritz. V

šetky možnosti nastavení sa vypíšu pomocu prepínača ```-h```.

Generovanie špeciálnych stavov je možné iba pre šifru Spritz.

Pre vygenerovanie stavov vo formáte pre [SMT nástroj](../smt) treba použiť prepínač ```--smt```. Nastavenia pre prednastavenie hodnôt v stave a prefix bežiaceho kľúča s prepínačom ```--smt``` nemajú žiadny efekt, tieto informácie SMT nástroj nepoužije.
