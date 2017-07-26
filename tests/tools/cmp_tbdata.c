#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <string.h>

int line = 0;
char buffer1[8192];
char buffer2[8192];

void check(bool ok)
{
	if (ok)
		return;
	fprintf(stderr, "Error in testbench output compare (line=%d):\n-%s\n+%s\n", line, buffer1, buffer2);
	exit(1);
}

int main(int argc, char **argv)
{
	FILE *f1, *f2;
	bool eof1, eof2;
	int i;

	check(argc == 3);

	f1 = fopen(argv[1], "r");
	f2 = fopen(argv[2], "r");

	check(f1 && f2);

	while (!feof(f1) && !feof(f2))
	{
		line++;
		buffer1[0] = 0;
		buffer2[0] = 0;

		eof1 = fgets(buffer1, 1024, f1) == NULL;
		eof2 = fgets(buffer2, 1024, f2) == NULL;

		if (*buffer1 && buffer1[strlen(buffer1)-1] == '\n')
			buffer1[strlen(buffer1)-1] = 0;

		if (*buffer2 && buffer2[strlen(buffer2)-1] == '\n')
			buffer2[strlen(buffer2)-1] = 0;

		check(eof1 == eof2);

		for (i = 0; buffer1[i] || buffer2[i]; i++)
		{
			check(buffer1[i] != 0 && buffer2[i] != 0);

			// first argument is the reference. An 'z' or 'x'
			// here means we don't care about the result.
			if (buffer1[i] == 'z' || buffer1[i] == 'x')
				continue;
			if (buffer1[i] == 'Z' || buffer1[i] == 'X')
				continue;

			check(buffer1[i] == buffer2[i]);
		}
	}

	check(feof(f1) && feof(f2));

	fclose(f1);
	fclose(f2);
	return 0;
}

