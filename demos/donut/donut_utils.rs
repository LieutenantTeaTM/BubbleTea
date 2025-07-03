const WIDTH: usize = 80;
const HEIGHT: usize = 24;
static mut OUTPUT: [char; WIDTH * HEIGHT] = [' '; WIDTH * HEIGHT];
static mut ZBUFFER: [f64; WIDTH * HEIGHT] = [0.0; WIDTH * HEIGHT];

pub fn set_data(xp: f64, yp: f64, ooz: f64, luminance: f64) {
    unsafe {
        let idx = xp as usize + WIDTH * yp as usize;
        if ooz > ZBUFFER[idx] {
            ZBUFFER[idx] = ooz;
            let lum_idx = luminance.max(0.0) as usize;
            let chars = ['.', ',', '-', '~', ':', ';', '=', '!', '*', '#', '$', '@'];
            let c = chars.get(lum_idx.min(chars.len() - 1)).unwrap_or(&' ');
            OUTPUT[idx] = *c;
        }
    }
}

pub fn clear_before_theta() {
    unsafe {
        for i in 0..(80 * 24) {
            OUTPUT[i] = ' ';
            ZBUFFER[i] = 0.0;
        }
    }
}

pub fn print_screen() {
    unsafe {
        print!("\x1b[H");
        for y in 0..HEIGHT {
            for x in 0..WIDTH {
                print!("{}", OUTPUT[x + WIDTH * y]);
            }
            println!();
        }
    }
}

pub fn get_cos(x: f64) -> f64 {
    x.cos()
}

pub fn get_sin(x: f64) -> f64 {
    x.sin()
}
