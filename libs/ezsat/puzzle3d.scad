
gap = 30;
layers = 0;
variant = 1;

module block(size_x, size_y, size_z, pos_x, pos_y, pos_z, idx)
{
	col = idx % 6 == 0 ? [ 0, 0, 1 ] :
	      idx % 6 == 1 ? [ 0, 1, 0 ] :
	      idx % 6 == 2 ? [ 0, 1, 1 ] :
	      idx % 6 == 3 ? [ 1, 0, 0 ] :
	      idx % 6 == 4 ? [ 1, 0, 1 ] :
	      idx % 6 == 5 ? [ 1, 1, 0 ] : [ 0, 0, 0 ];
	translate([-2.5, -2.5, 0] * (100+gap)) difference() {
		color(col) translate([pos_x, pos_y, pos_z] * (100 + gap))
			cube([size_x, size_y, size_z] * (100+gap) - [gap, gap, gap], false);
		if (layers > 0)
			color([0.3, 0.3, 0.3]) translate([0, 0, layers * (100+gap)] - [0.5, 0.5, 0.5] * gap)
				cube([5, 5, 5] * (100 + gap), false);
	}
}

if (variant == 1) {
	block(1,4,2,0,1,3,47);
	block(1,4,2,4,0,0,72);
	block(2,1,4,0,0,0,80);
	block(2,1,4,3,4,1,119);
	block(4,2,1,0,3,0,215);
	block(4,2,1,1,0,4,224);
	block(3,2,2,0,3,1,253);
	block(3,2,2,2,0,2,274);
	block(2,3,2,1,2,3,311);
	block(2,3,2,2,0,0,312);
	block(2,2,3,0,1,0,339);
	block(2,2,3,3,2,2,380);
}

if (variant == 2) {
	block(1,2,4,0,0,1,1);
	block(1,2,4,4,3,0,38);
	block(2,4,1,0,1,0,125);
	block(2,4,1,3,0,4,154);
	block(4,1,2,0,4,3,179);
	block(4,1,2,1,0,0,180);
	block(3,2,2,0,2,3,251);
	block(3,2,2,2,1,0,276);
	block(2,3,2,0,2,1,297);
	block(2,3,2,3,0,2,326);
	block(2,2,3,1,0,2,350);
	block(2,2,3,2,3,0,369);
}

if (variant == 3) {
	block(1,4,2,0,0,3,43);
	block(1,4,2,4,1,0,76);
	block(2,1,4,0,4,0,88);
	block(2,1,4,3,0,1,111);
	block(4,2,1,0,0,0,200);
	block(4,2,1,1,3,4,239);
	block(3,2,2,0,0,1,241);
	block(3,2,2,2,3,2,286);
	block(2,3,2,1,0,3,303);
	block(2,3,2,2,2,0,320);
	block(2,2,3,0,2,0,342);
	block(2,2,3,3,1,2,377);
}

if (variant == 4) {
	block(1,2,4,0,3,1,7);
	block(1,2,4,4,0,0,32);
	block(2,4,1,0,0,0,120);
	block(2,4,1,3,1,4,159);
	block(4,1,2,0,0,3,163);
	block(4,1,2,1,4,0,196);
	block(3,2,2,0,1,3,247);
	block(3,2,2,2,2,0,280);
	block(2,3,2,0,0,1,289);
	block(2,3,2,3,2,2,334);
	block(2,2,3,1,3,2,359);
	block(2,2,3,2,0,0,360);
}

