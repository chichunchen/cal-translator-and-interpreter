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
int main() {
    int n;
    int cp;
    int found;
    int cf1;
    int cf1s;
    int cf2;
    int pr;
    n = getint();
    cp = 2;
    while(1) {
        if (!(n>0)) break;
        found = 0;
        cf1 = 2;
        cf1s = (cf1*cf1);
        while(1) {
            if (!(cf1s<=cp)) break;
            cf2 = 2;
            pr = (cf1*cf2);
            while(1) {
                if (!(pr<=cp)) break;
                if ((pr==cp)) {
                    found = 1;
                }
                cf2 = (cf2+1);
                pr = (cf1*cf2);
            }
            cf1 = (cf1+1);
            cf1s = (cf1*cf1);
        }
        if ((found==0)) {
            putint(cp);
            n = (n-1);
        }
        cp = (cp+1);
    }
    return 0;
}val p2 : unit = ()
```
