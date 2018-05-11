#include <gmp.h>

#define target 50000

int main(void)
{
    mpz_t f;
    mpz_t c;
    mpz_t one;

    mpz_init_set_ui(f, 1);
    mpz_init_set_ui(c, 1);
    mpz_init_set_ui(one, 1);

    for (int i = 0; i < target; ++i) {
        mpz_mul(f, f, c);
        mpz_add(c, c, one);
    }

    gmp_printf("%Zx", f);
}
