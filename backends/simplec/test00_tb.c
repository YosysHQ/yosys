#include <stdio.h>
#include <assert.h>
#include "test00_uut.c"

uint32_t xorshift32()
{
	static uint32_t x32 = 314159265;
	x32 ^= x32 << 13;
	x32 ^= x32 >> 17;
	x32 ^= x32 << 5;
	return x32;
}

int main()
{
	struct test_state_t state;
	uint32_t a, b, c, x, y, z, w;
	bool first_eval = true;

	for (int i = 0; i < 10; i++)
	{
		a = xorshift32();
		b = xorshift32();
		c = xorshift32();

		x = (a & b) | c;
		y = a & (b | c);
		z = a ^ b ^ c;
		w = z;

		state.a.value_7_0   = a;
		state.a.value_15_8  = a >> 8;
		state.a.value_23_16 = a >> 16;
		state.a.value_31_24 = a >> 24;

		state.b.value_7_0   = b;
		state.b.value_15_8  = b >> 8;
		state.b.value_23_16 = b >> 16;
		state.b.value_31_24 = b >> 24;

		state.c.value_7_0   = c;
		state.c.value_15_8  = c >> 8;
		state.c.value_23_16 = c >> 16;
		state.c.value_31_24 = c >> 24;

		if (first_eval) {
			first_eval = false;
			test_init(&state);
		} else {
			test_eval(&state);
		}

		uint32_t uut_x = 0;
		uut_x |= (uint32_t)state.x.value_7_0;
		uut_x |= (uint32_t)state.x.value_15_8  << 8;
		uut_x |= (uint32_t)state.x.value_23_16 << 16;
		uut_x |= (uint32_t)state.x.value_31_24 << 24;

		uint32_t uut_y = 0;
		uut_y |= (uint32_t)state.y.value_7_0;
		uut_y |= (uint32_t)state.y.value_15_8  << 8;
		uut_y |= (uint32_t)state.y.value_23_16 << 16;
		uut_y |= (uint32_t)state.y.value_31_24 << 24;

		uint32_t uut_z = 0;
		uut_z |= (uint32_t)state.z.value_7_0;
		uut_z |= (uint32_t)state.z.value_15_8  << 8;
		uut_z |= (uint32_t)state.z.value_23_16 << 16;
		uut_z |= (uint32_t)state.z.value_31_24 << 24;

		uint32_t uut_w = 0;
		uut_w |= (uint32_t)state.w.value_7_0;
		uut_w |= (uint32_t)state.w.value_15_8  << 8;
		uut_w |= (uint32_t)state.w.value_23_16 << 16;
		uut_w |= (uint32_t)state.w.value_31_24 << 24;

		printf("---\n");
		printf("A: 0x%08x\n", a);
		printf("B: 0x%08x\n", b);
		printf("C: 0x%08x\n", c);
		printf("X: 0x%08x 0x%08x\n", x, uut_x);
		printf("Y: 0x%08x 0x%08x\n", y, uut_y);
		printf("Z: 0x%08x 0x%08x\n", z, uut_z);
		printf("W: 0x%08x 0x%08x\n", w, uut_w);

		assert(x == uut_x);
		assert(y == uut_y);
		assert(z == uut_z);
		assert(w == uut_w);
	}

	return 0;
}
