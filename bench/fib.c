#include <gmp.h>

#define target 200000

int main(void)
{
    mpz_t f0, f1;
    mpz_init_set_ui(f0, 1);
    mpz_init_set_ui(f1, 1);

    for (int i = 0; i < target; ++i) {
        mpz_add(f1, f1, f0);
        mpz_sub(f0, f1, f0);
    }

    gmp_printf("%Zx", f1);
}
