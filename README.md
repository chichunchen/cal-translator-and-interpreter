A3 Translator

```
#include <stdio.h>
#include <stdlib.h>
int getint() {
    int n;
    scanf("%d", &n);
    return n;
}
void putint(int n) {
    printf("%d\n", n);
}
n = getint();
int cp = 2;
while(1) {
if (!(n>0)) break;
int found = 0;
int cf1 = 2;
int cf1s = (cf1*cf1);
while(1) {
if (!(cf1s<=cp)) break;
int cf2 = 2;
int pr = (cf1*cf2);
while(1) {
if (!(pr<=cp)) break;
if ((pr==cp)) {
int found = 1;
}
int cf2 = (cf2+1);
int pr = (cf1*cf2);
}
int cf1 = (cf1+1);
int cf1s = (cf1*cf1);
}
if ((found==0)) {
putint(cp);
int n = (n-1);
}
int cp = (cp+1);
}
- : unit = ()
```
