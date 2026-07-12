import machine
import random
import time
from micropython import const
import ustruct as struct
import math
import dht  # DHT11/DHT22 sensor support
from machine import I2S, Pin
import array

# ILI9341 command set
ILI9341_SWRESET = const(0x01)
ILI9341_SLPOUT = const(0x11)
ILI9341_DISPON = const(0x29)
ILI9341_CASET = const(0x2A)
ILI9341_PASET = const(0x2B)
ILI9341_RAMWR = const(0x2C)
ILI9341_MADCTL = const(0x36)
ILI9341_PIXFMT = const(0x3A)
ILI9341_PWCTR1 = const(0xC0)
ILI9341_PWCTR2 = const(0xC1)
ILI9341_VMCTR1 = const(0xC5)
ILI9341_VMCTR2 = const(0xC7)
ILI9341_FRMCTR1 = const(0xB1)
ILI9341_DFUNCTR = const(0xB6)
ILI9341_GAMMASET = const(0x26)
ILI9341_GMCTRP1 = const(0xE0)
ILI9341_GMCTRN1 = const(0xE1)

MADCTL_MX = const(0x40)
MADCTL_BGR = const(0x08)

# Color palette (RGB565)
GREEN_LIGHT = const(0x87E0)
GREEN_DARK = const(0x0400)
BLUE_LIGHT = const(0x3D7F)
BLUE_DARK = const(0x001F)
ORANGE = const(0xFD20)
RED = const(0xF800)
YELLOW = const(0xFFE0)
WHITE = const(0xFFFF)
BLACK = const(0x0000)
GRAY_LIGHT = const(0xCE79)
GRAY_DARK = const(0x7BEF)
BROWN = const(0x8200)

# Touch controller commands (XPT2046/ADS7843)
TOUCH_CMD_X = const(0x90)
TOUCH_CMD_Y = const(0xD0)

def delay_ms(ms):
    time.sleep_ms(ms)

def color565(r, g=0, b=0):
    """Convert RGB to 565 format"""
    try:
        r, g, b = r
    except TypeError:
        pass
    return (r & 0xf8) << 8 | (g & 0xfc) << 3 | b >> 3

class TouchController:
    def __init__(self, spi, cs, irq):
        self.spi = spi
        self.cs = cs
        self.irq = irq
        self.cs.on()  # CS high (inactive)

        # Calibration values, may need adjusting per panel
        self.cal_x_min = 200
        self.cal_x_max = 3800
        self.cal_y_min = 200
        self.cal_y_max = 3800

        self.test_connection()

    def test_connection(self):
        """Tests the connection to the touch controller"""
        print("Testing touch controller connection...")

        irq_state = self.irq.value()
        print(f"IRQ pin state: {irq_state} (1=no touch, 0=touch detected)")

        try:
            test_x = self.read_touch_raw(TOUCH_CMD_X)
            test_y = self.read_touch_raw(TOUCH_CMD_Y)
            print(f"Touch test values: X={test_x}, Y={test_y}")

            if test_x == 0 and test_y == 0:
                print("Warning: touch controller not responding correctly")
            else:
                print("Touch controller responding")

        except Exception as e:
            print(f"Touch controller error: {e}")

    def read_touch_raw(self, cmd):
        """Reads a raw touch sample"""
        self.cs.off()
        delay_ms(1)

        self.spi.write(bytes([cmd]))

        delay_ms(1)
        result = self.spi.read(2)

        delay_ms(1)
        self.cs.on()

        if len(result) == 2:
            # 12-bit resolution (ADS7843/XPT2046)
            value = (result[0] << 8 | result[1]) >> 3
            return value & 0x0FFF
        return 0

    def get_touch(self):
        """Returns the touch position, or None if there's no touch"""
        irq_state = self.irq.value()

        if irq_state == 1:  # IRQ is HIGH when not pressed
            return None

        # Average a few samples for stability
        x_sum = y_sum = 0
        valid_readings = 0

        for i in range(3):
            x_raw = self.read_touch_raw(TOUCH_CMD_X)
            y_raw = self.read_touch_raw(TOUCH_CMD_Y)

            if i == 0:
                print(f"Touch raw: X={x_raw}, Y={y_raw}, IRQ={irq_state}")

            if x_raw > 100 and y_raw > 100 and x_raw < 4000 and y_raw < 4000:
                x_sum += x_raw
                y_sum += y_raw
                valid_readings += 1

        if valid_readings == 0:
            print("No valid touch readings")
            return None

        x_avg = x_sum // valid_readings
        y_avg = y_sum // valid_readings

        # Map to screen coordinates
        x = int((x_avg - self.cal_x_min) * 320 / (self.cal_x_max - self.cal_x_min))
        y = int((y_avg - self.cal_y_min) * 240 / (self.cal_y_max - self.cal_y_min))

        x = max(0, min(319, x))
        y = max(0, min(239, y))

        print(f"Touch calculated: X={x}, Y={y} (raw avg: {x_avg}, {y_avg})")
        return (x, y)

class SmartPlantDisplay:
    def __init__(self, spi, dc, reset, cs=None, touch=None):
        self.spi = spi
        self.dc = dc
        self.reset = reset
        self.cs = cs
        self.touch = touch
        self.width = 320
        self.height = 240
        self.current_screen = 0
        self.last_update = 0
        self.last_touch_time = 0
        self.manual_mode = False  # touch disables auto screen switching
        self.last_drawn_screen = -1
        self.screen_needs_redraw = True
        self.last_light_value = 0
        self.data_needs_update = False  # value-only update without full redraw

        # Motion sensor tracking
        self.last_motion_time = 0
        self.motion_timeout = 30000  # ms, adjustable
        self.motion_timeout_seconds = 30  # for UI display, adjustable
        self.last_motion_check = 0
        self.audio_played = False
        self.reward_played = False

        # I2S audio system for punishment/reward sounds
        self.i2s = None
        self.setup_audio_system()

        # Last displayed values, for change detection
        self.last_displayed_values = {
            'light': 0,
            'temperature': 0,
            'humidity': 0,
            'plant_health': 0
        }

        # Sensors
        self.light_sensor = machine.ADC(machine.Pin(28))  # GP28 = ADC2, light sensor
        self.dht_sensor = dht.DHT11(machine.Pin(27))      # GP27, temp/humidity sensor
        self.motion_pin = machine.Pin(26, machine.Pin.IN) # GP26, motion sensor

        current_time = time.ticks_ms()
        self.last_motion_time = current_time  # start as if motion was just detected
        print(f"Motion sensor initialized - {self.motion_timeout_seconds}s timer started")

        # Simulated sensor data, used as fallback when a real sensor is unavailable
        self.sensor_data = {
            'temperature': 22.5,
            'humidity': 65,
            'light': 750,
            'light_voltage': 1.65,
            'light_raw': 32767,
            'water_level': 80,
            'plant_health': 85
        }

    # Low-level display functions
    def dc_low(self):
        self.dc.off()

    def dc_high(self):
        self.dc.on()

    def cs_low(self):
        if self.cs:
            self.cs.off()

    def cs_high(self):
        if self.cs:
            self.cs.on()

    def write_cmd(self, cmd):
        self.cs_low()
        self.dc_low()
        self.spi.write(bytes([cmd]))
        self.cs_high()

    def write_data(self, data):
        self.cs_low()
        self.dc_high()
        if isinstance(data, int):
            self.spi.write(bytes([data]))
        else:
            self.spi.write(data)
        self.cs_high()

    def write_cmd_data(self, cmd, data=None):
        self.cs_low()
        self.dc_low()
        self.spi.write(bytes([cmd]))
        if data is not None:
            self.dc_high()
            if isinstance(data, int):
                self.spi.write(bytes([data]))
            else:
                self.spi.write(data)
        self.cs_high()

    def init(self):
        """Initializes the display controller"""
        print("Initializing display...")

        if self.reset:
            self.reset.off()
            delay_ms(100)
            self.reset.on()
            delay_ms(100)

        self.write_cmd(ILI9341_SWRESET)
        delay_ms(150)

        self.write_cmd(ILI9341_SLPOUT)
        delay_ms(120)

        self.write_cmd_data(0xCB, bytes([0x39, 0x2C, 0x00, 0x34, 0x02]))
        self.write_cmd_data(0xCF, bytes([0x00, 0xC1, 0x30]))
        self.write_cmd_data(ILI9341_PWCTR1, 0x23)
        self.write_cmd_data(ILI9341_PWCTR2, 0x10)
        self.write_cmd_data(ILI9341_VMCTR1, bytes([0x3e, 0x28]))
        self.write_cmd_data(ILI9341_VMCTR2, 0x86)
        self.write_cmd_data(ILI9341_MADCTL, 0x88)  # MY(0x80) | BGR(0x08), 270° rotation
        self.write_cmd_data(ILI9341_PIXFMT, 0x55)
        self.write_cmd_data(ILI9341_FRMCTR1, bytes([0x00, 0x18]))

        self.write_cmd(ILI9341_DISPON)
        delay_ms(100)

        print("Display ready")

    def set_window(self, x0, y0, x1, y1):
        self.write_cmd_data(ILI9341_CASET, struct.pack(">HH", x0, x1))
        self.write_cmd_data(ILI9341_PASET, struct.pack(">HH", y0, y1))
        self.write_cmd(ILI9341_RAMWR)

    def fill_rect(self, x, y, w, h, color):
        if x + w > self.width:
            w = self.width - x
        if y + h > self.height:
            h = self.height - y

        self.set_window(x, y, x + w - 1, y + h - 1)
        pixel_data = struct.pack(">H", color)

        self.cs_low()
        self.dc_high()
        for _ in range(w * h):
            self.spi.write(pixel_data)
        self.cs_high()

    def fill(self, color):
        self.fill_rect(0, 0, self.width, self.height, color)

    def pixel(self, x, y, color):
        if 0 <= x < self.width and 0 <= y < self.height:
            self.set_window(x, y, x, y)
            self.write_data(struct.pack(">H", color))

    def hline(self, x, y, w, color):
        self.fill_rect(x, y, w, 1, color)

    def vline(self, x, y, h, color):
        self.fill_rect(x, y, 1, h, color)

    # UI drawing helpers
    def draw_rounded_rect(self, x, y, w, h, radius, color):
        """Draws a rounded rectangle"""
        self.fill_rect(x + radius, y, w - 2*radius, h, color)
        self.fill_rect(x, y + radius, radius, h - 2*radius, color)
        self.fill_rect(x + w - radius, y + radius, radius, h - 2*radius, color)

        # Corners
        for i in range(radius):
            for j in range(radius):
                if i*i + j*j <= radius*radius:
                    self.pixel(x + radius - i, y + radius - j, color)
                    self.pixel(x + w - radius + i, y + radius - j, color)
                    self.pixel(x + radius - i, y + h - radius + j, color)
                    self.pixel(x + w - radius + i, y + h - radius + j, color)

    def draw_circle(self, cx, cy, radius, color):
        """Draws a filled circle"""
        for x in range(-radius, radius + 1):
            for y in range(-radius, radius + 1):
                if x*x + y*y <= radius*radius:
                    self.pixel(cx + x, cy + y, color)

    def draw_progress_bar(self, x, y, w, h, value, max_value, bg_color, fg_color):
        """Draws a progress bar"""
        self.draw_rounded_rect(x, y, w, h, 3, bg_color)

        progress_w = int((value / max_value) * (w - 4))
        if progress_w > 0:
            self.draw_rounded_rect(x + 2, y + 2, progress_w, h - 4, 2, fg_color)

    def draw_digit(self, x, y, digit, size, color):
        """Draws a single digit as a 7-segment display"""
        segments = [
            [1,1,1,1,1,1,0], # 0
            [0,1,1,0,0,0,0], # 1
            [1,1,0,1,1,0,1], # 2
            [1,1,1,1,0,0,1], # 3
            [0,1,1,0,0,1,1], # 4
            [1,0,1,1,0,1,1], # 5
            [1,0,1,1,1,1,1], # 6
            [1,1,1,0,0,0,0], # 7
            [1,1,1,1,1,1,1], # 8
            [1,1,1,1,0,1,1]  # 9
        ]

        if 0 <= digit <= 9:
            seg = segments[digit]
            w = size * 6
            h = size * 10

            if seg[0]: self.fill_rect(x+size, y, w-2*size, size, color)           # top
            if seg[1]: self.fill_rect(x+w-size, y+size, size, h//2-size, color)  # top right
            if seg[2]: self.fill_rect(x+w-size, y+h//2, size, h//2-size, color)  # bottom right
            if seg[3]: self.fill_rect(x+size, y+h-size, w-2*size, size, color)   # bottom
            if seg[4]: self.fill_rect(x, y+h//2, size, h//2-size, color)         # bottom left
            if seg[5]: self.fill_rect(x, y+size, size, h//2-size, color)         # top left
            if seg[6]: self.fill_rect(x+size, y+h//2-size//2, w-2*size, size, color) # middle

    def draw_number(self, x, y, number, size, color):
        """Draws a multi-digit number"""
        num_str = str(int(number))
        digit_width = size * 8

        for i, digit_char in enumerate(num_str):
            digit = int(digit_char)
            digit_x = x + i * digit_width
            self.draw_digit(digit_x, y, digit, size, color)

    def draw_icon_plant(self, x, y, size, color):
        """Draws a plant icon"""
        stem_x = x + size // 2
        self.vline(stem_x, y + size//3, size//2, GREEN_DARK)

        self.draw_circle(x + size//4, y + size//4, size//6, color)
        self.draw_circle(x + 3*size//4, y + size//4, size//6, color)
        self.draw_circle(x + size//2, y + size//6, size//5, color)

    def draw_icon_water(self, x, y, size, color):
        """Draws a water drop icon"""
        self.draw_circle(x + size//2, y + size//2, size//3, color)

    def draw_icon_temperature(self, x, y, size, color):
        """Draws a thermometer icon"""
        therm_x = x + size//2
        self.vline(therm_x, y + size//4, size//2, color)
        self.draw_circle(therm_x, y + 3*size//4, size//8, color)

    def draw_icon_sun(self, x, y, size, color):
        """Draws a sun icon"""
        center_x, center_y = x + size//2, y + size//2
        radius = size//4

        for angle in range(0, 360, 45):
            angle_rad = angle * 3.14159 / 180
            x1 = center_x + int(radius * 1.5 * math.cos(angle_rad))
            y1 = center_y + int(radius * 1.5 * math.sin(angle_rad))
            x2 = center_x + int(radius * 2 * math.cos(angle_rad))
            y2 = center_y + int(radius * 2 * math.sin(angle_rad))

            for i in range(3):
                if 0 <= x1+i < self.width and 0 <= y1 < self.height:
                    self.pixel(x1+i, y1, color)

        self.draw_circle(center_x, center_y, radius, color)

    def read_light_sensor(self):
        """Reads the light sensor (ADC)"""
        try:
            raw = self.light_sensor.read_u16()  # 0 to 65535
            voltage = raw * 3.3 / 65535

            # Map to a lux-like range (0-1000); may need calibration
            light_value = int((raw / 65535) * 1000)

            return light_value, voltage, raw
        except Exception as e:
            print(f"Light sensor error: {e}")
            return 500, 1.65, 32767  # fallback values

    def read_temp_humidity_sensor(self):
        """Reads the DHT11 temperature/humidity sensor"""
        try:
            self.dht_sensor.measure()
            temperature = self.dht_sensor.temperature()
            humidity = self.dht_sensor.humidity()

            print(f"DHT11 - Temp: {temperature}C, Humidity: {humidity}%")
            return temperature, humidity

        except OSError as e:
            print(f"DHT11 sensor error: {e} (not connected or faulty?)")
            return None, None
        except Exception as e:
            print(f"DHT11 unknown error: {e}")
            return None, None

    def read_motion_sensor(self):
        """Reads the motion sensor and triggers reward/punishment audio based on the timeout"""
        try:
            current_time = time.ticks_ms()
            motion_state = self.motion_pin.value()

            if motion_state == 1:  # motion detected -> reward
                self.last_motion_time = current_time
                self.audio_played = False

                # Only play the reward sound once per motion event
                if not self.reward_played:
                    print("Motion detected - watering detected")
                    self.play_reward_sound()
                    self.reward_played = True

                return True
            else:
                self.reward_played = False

            # Check the timeout every 5s to avoid spamming
            if time.ticks_diff(current_time, self.last_motion_check) > 5000:
                self.last_motion_check = current_time

                if time.ticks_diff(current_time, self.last_motion_time) > self.motion_timeout:
                    print(f"No motion for {self.motion_timeout_seconds}+ seconds - punishment")

                    # Only play the punishment sound once per timeout period
                    if not self.audio_played:
                        self.play_punishment_sound()
                        self.audio_played = True

            return False

        except Exception as e:
            print(f"Motion sensor error: {e}")
            return False

    def setup_audio_system(self):
        """Initializes the I2S audio system"""
        try:
            self.i2s = I2S(
                0,
                sck=Pin(10),    # BCLK
                ws=Pin(11),     # LRC / WS
                sd=Pin(12),     # DIN
                mode=I2S.TX,
                bits=16,
                format=I2S.MONO,
                rate=22050,
                ibuf=20000,
            )
            print("I2S audio system initialized (GP10=BCLK, GP11=WS, GP12=DIN)")
        except Exception as e:
            print(f"I2S audio system error: {e}")
            self.i2s = None

    def play_punishment_sound(self):
        """Plays the punishment sound: a 5s, 3000 Hz sine wave"""
        if not self.i2s:
            print("I2S not available - no sound")
            return

        try:
            print("Punishment: playing sine wave (5s, 3000 Hz)")

            sample_rate = 22050
            frequency = 3000
            amplitude = 32767  # max for 16-bit audio
            duration = 5
            samples_per_cycle = sample_rate // frequency

            sine_wave = array.array("h", [
                int(amplitude * math.sin(2 * math.pi * i / samples_per_cycle))
                for i in range(samples_per_cycle)
            ])

            num_cycles = int(sample_rate * duration // samples_per_cycle)
            for cycle in range(num_cycles):
                self.i2s.write(sine_wave)
                if cycle % 50 == 0:
                    time.sleep_ms(1)

            print("Punishment sound finished")

        except Exception as e:
            print(f"Audio playback error: {e}")

    def play_reward_sound(self):
        """Plays the reward sound: a short major-chord melody"""
        if not self.i2s:
            print("I2S not available - no reward sound")
            return

        try:
            print("Reward: playing melody (good plant care!)")

            sample_rate = 22050
            amplitude = 16383  # quieter than the punishment sound
            duration = 2

            # C major triad progression
            frequencies = [
                261.63,  # C4
                329.63,  # E4
                392.00,  # G4
                523.25   # C5
            ]

            note_duration = 0.5

            for freq in frequencies:
                samples_per_cycle = sample_rate // int(freq)

                sine_wave = array.array("h", [
                    int(amplitude * math.sin(2 * math.pi * i / samples_per_cycle))
                    for i in range(samples_per_cycle)
                ])

                num_cycles = int(sample_rate * note_duration // samples_per_cycle)
                for cycle in range(num_cycles):
                    self.i2s.write(sine_wave)
                    if cycle % 20 == 0:
                        time.sleep_ms(1)

            print("Reward melody finished")

        except Exception as e:
            print(f"Reward audio error: {e}")

    def cleanup_audio(self):
        """Tears down the audio system"""
        if self.i2s:
            try:
                self.i2s.deinit()
                print("I2S audio system stopped")
            except:
                pass
            self.i2s = None

    def show_main_screen(self):
        """Draws the main dashboard screen"""
        self.fill(BLACK)

        y_start = 20

        # Row 1: temperature (1 box) + light (2 boxes)
        color = GRAY_LIGHT

        # Temperature widget
        self.draw_rounded_rect(10, y_start, 90, 80, 8, color)
        self.draw_icon_temperature(20, y_start + 10, 30, ORANGE)
        self.draw_number(20, y_start + 45, self.sensor_data['temperature'], 2, ORANGE)

        # Light widget, spans 2 boxes
        light_value = int(self.sensor_data['light'])
        light_color = self.get_light_quality_color(light_value)
        light_description = self.get_light_quality_description(light_value)

        self.draw_rounded_rect(110, y_start, 200, 80, 8, color)
        self.draw_icon_sun(120, y_start + 10, 60, light_color)

        # Light quality label, next to the icon
        text_x = 190
        text_y = y_start + 20

        if len(light_description) > 10:
            words = light_description.split()
            if len(words) >= 2:
                self.draw_simple_text_2x(text_x, text_y, words[0], light_color)
                self.draw_simple_text_2x(text_x, text_y + 20, words[1], light_color)
            else:
                short_desc = light_description[:10]
                self.draw_simple_text_2x(text_x, text_y, short_desc, light_color)
        else:
            self.draw_simple_text_2x(text_x, text_y, light_description, light_color)

        # Row 2: humidity (1 box) + plant health (2 boxes)
        self.draw_rounded_rect(10, y_start + 90, 90, 80, 8, color)
        self.draw_icon_water(20, y_start + 100, 30, BLUE_LIGHT)
        self.draw_number(20, y_start + 135, self.sensor_data['humidity'], 2, BLUE_LIGHT)

        self.draw_rounded_rect(110, y_start + 90, 200, 80, 8, color)
        health = self.sensor_data['plant_health']

        if health > 80:
            status_color = GREEN_LIGHT
        elif health > 60:
            status_color = YELLOW
        else:
            status_color = RED

        self.draw_progress_bar(120, y_start + 110, 180, 25, health, 100, GRAY_DARK, status_color)
        self.draw_simple_text(115, y_start + 95, "HEALTH", status_color)
        self.draw_number(270, y_start + 95, health, 1, status_color)

        self.draw_bottom_navigation_bar()

    def show_detail_screen(self):
        """Draws the detail screen with larger sensor readouts"""
        self.fill(BLACK)

        y = 20

        # Temperature
        self.fill_rect(10, y, 300, 40, GRAY_LIGHT)
        self.draw_icon_temperature(20, y + 5, 30, ORANGE)
        temp_str = f"{self.sensor_data['temperature']:.1f}"
        self.draw_number(200, y + 5, float(temp_str), 3, ORANGE)

        y += 50

        # Light sensor
        self.fill_rect(10, y, 300, 40, GRAY_LIGHT)
        light_value = self.sensor_data['light']
        light_color = self.get_light_quality_color(light_value)
        light_description = self.get_light_quality_description(light_value)

        self.draw_icon_sun(20, y + 5, 30, light_color)
        self.draw_progress_bar(70, y + 10, 150, 20, light_value, 1000, GRAY_DARK, light_color)
        self.draw_simple_text(230, y + 15, light_description, light_color)

        y += 50

        # Water tank level
        self.fill_rect(10, y, 300, 40, GRAY_LIGHT)
        self.draw_icon_water(20, y + 5, 30, BLUE_LIGHT)
        water_level = self.sensor_data['water_level']
        self.draw_progress_bar(70, y + 10, 200, 20, water_level, 100, GRAY_DARK, BLUE_LIGHT)
        self.draw_number(280, y + 15, water_level, 2, BLUE_LIGHT)

        self.draw_bottom_navigation_bar()

    def show_settings_screen(self):
        """Draws the settings screen for the motion timeout"""
        self.fill(BLACK)

        header_y = 10
        self.fill_rect(10, header_y, 300, 30, GRAY_DARK)

        self.draw_simple_text(15, header_y + 8, "MOTION:", WHITE)

        timeout_x = 200
        self.draw_number(timeout_x, header_y + 5, self.motion_timeout_seconds, 2, WHITE)
        self.draw_simple_text(timeout_x + 50, header_y + 15, "s", WHITE)

        settings_y = 50

        # -10s button
        self.draw_rounded_rect(20, settings_y, 60, 40, 8, RED)
        self.draw_simple_text(35, settings_y + 18, "-10", WHITE)

        # Current value
        self.draw_rounded_rect(90, settings_y, 140, 40, 8, BLUE_LIGHT)
        center_x = 90 + 70 - (len(str(self.motion_timeout_seconds)) * 8)  # centered
        self.draw_number(center_x, settings_y + 10, self.motion_timeout_seconds, 3, BLACK)

        # +10s button
        self.draw_rounded_rect(240, settings_y, 60, 40, 8, GREEN_LIGHT)
        self.draw_simple_text(255, settings_y + 18, "+10", BLACK)

        # Fine adjustment (+/-5s)
        fine_y = settings_y + 50

        self.draw_rounded_rect(50, fine_y, 50, 30, 5, ORANGE)
        self.draw_simple_text(65, fine_y + 12, "-5", BLACK)

        self.draw_rounded_rect(220, fine_y, 50, 30, 5, ORANGE)
        self.draw_simple_text(235, fine_y + 12, "+5", BLACK)

        # Presets
        preset_y = fine_y + 40
        presets = [15, 30, 60, 120]  # 15s, 30s, 1min, 2min
        preset_colors = [YELLOW, GREEN_LIGHT, BLUE_LIGHT, GRAY_LIGHT]
        preset_labels = ["15s", "30s", "1m", "2m"]

        for i, (preset, color, label) in enumerate(zip(presets, preset_colors, preset_labels)):
            x = 20 + i * 70
            self.draw_rounded_rect(x, preset_y, 60, 25, 5, color)

            label_x = x + 30 - (len(label) * 4)  # centered
            self.draw_simple_text(label_x, preset_y + 10, label, BLACK)

        info_y = preset_y + 35
        self.fill_rect(10, info_y, 300, 20, GRAY_DARK)
        self.draw_simple_text(15, info_y + 6, "Touch buttons to change timeout", WHITE)

        self.draw_bottom_navigation_bar()

    def draw_simple_text(self, x, y, text, color):
        """Draws text using a simple 5x7 pixel font"""
        font = {
            'A': [[0,1,1,1,0], [1,0,0,0,1], [1,0,0,0,1], [1,1,1,1,1], [1,0,0,0,1], [1,0,0,0,1], [0,0,0,0,0]],
            'B': [[1,1,1,1,0], [1,0,0,0,1], [1,1,1,1,0], [1,0,0,0,1], [1,0,0,0,1], [1,1,1,1,0], [0,0,0,0,0]],
            'C': [[0,1,1,1,0], [1,0,0,0,1], [1,0,0,0,0], [1,0,0,0,0], [1,0,0,0,1], [0,1,1,1,0], [0,0,0,0,0]],
            'D': [[1,1,1,1,0], [1,0,0,0,1], [1,0,0,0,1], [1,0,0,0,1], [1,0,0,0,1], [1,1,1,1,0], [0,0,0,0,0]],
            'E': [[1,1,1,1,1], [1,0,0,0,0], [1,1,1,1,0], [1,0,0,0,0], [1,0,0,0,0], [1,1,1,1,1], [0,0,0,0,0]],
            'F': [[1,1,1,1,1], [1,0,0,0,0], [1,1,1,1,0], [1,0,0,0,0], [1,0,0,0,0], [1,0,0,0,0], [0,0,0,0,0]],
            'G': [[0,1,1,1,0], [1,0,0,0,1], [1,0,0,0,0], [1,0,1,1,1], [1,0,0,0,1], [0,1,1,1,0], [0,0,0,0,0]],
            'H': [[1,0,0,0,1], [1,0,0,0,1], [1,1,1,1,1], [1,0,0,0,1], [1,0,0,0,1], [1,0,0,0,1], [0,0,0,0,0]],
            'I': [[0,1,1,1,0], [0,0,1,0,0], [0,0,1,0,0], [0,0,1,0,0], [0,0,1,0,0], [0,1,1,1,0], [0,0,0,0,0]],
            'K': [[1,0,0,0,1], [1,0,0,1,0], [1,0,1,0,0], [1,1,0,0,0], [1,0,1,0,0], [1,0,0,1,0], [0,0,0,0,0]],
            'L': [[1,0,0,0,0], [1,0,0,0,0], [1,0,0,0,0], [1,0,0,0,0], [1,0,0,0,0], [1,1,1,1,1], [0,0,0,0,0]],
            'M': [[1,0,0,0,1], [1,1,0,1,1], [1,0,1,0,1], [1,0,0,0,1], [1,0,0,0,1], [1,0,0,0,1], [0,0,0,0,0]],
            'N': [[1,0,0,0,1], [1,1,0,0,1], [1,0,1,0,1], [1,0,0,1,1], [1,0,0,0,1], [1,0,0,0,1], [0,0,0,0,0]],
            'O': [[0,1,1,1,0], [1,0,0,0,1], [1,0,0,0,1], [1,0,0,0,1], [1,0,0,0,1], [0,1,1,1,0], [0,0,0,0,0]],
            'P': [[1,1,1,1,0], [1,0,0,0,1], [1,1,1,1,0], [1,0,0,0,0], [1,0,0,0,0], [1,0,0,0,0], [0,0,0,0,0]],
            'R': [[1,1,1,1,0], [1,0,0,0,1], [1,1,1,1,0], [1,0,1,0,0], [1,0,0,1,0], [1,0,0,0,1], [0,0,0,0,0]],
            'S': [[0,1,1,1,1], [1,0,0,0,0], [0,1,1,1,0], [0,0,0,0,1], [0,0,0,0,1], [1,1,1,1,0], [0,0,0,0,0]],
            'T': [[1,1,1,1,1], [0,0,1,0,0], [0,0,1,0,0], [0,0,1,0,0], [0,0,1,0,0], [0,0,1,0,0], [0,0,0,0,0]],
            'U': [[1,0,0,0,1], [1,0,0,0,1], [1,0,0,0,1], [1,0,0,0,1], [1,0,0,0,1], [0,1,1,1,0], [0,0,0,0,0]],
            'V': [[1,0,0,0,1], [1,0,0,0,1], [1,0,0,0,1], [1,0,0,0,1], [0,1,0,1,0], [0,0,1,0,0], [0,0,0,0,0]],
            'Y': [[1,0,0,0,1], [1,0,0,0,1], [0,1,0,1,0], [0,0,1,0,0], [0,0,1,0,0], [0,0,1,0,0], [0,0,0,0,0]],
            '0': [[0,1,1,1,0], [1,0,0,0,1], [1,0,0,0,1], [1,0,0,0,1], [1,0,0,0,1], [0,1,1,1,0], [0,0,0,0,0]],
            '1': [[0,0,1,0,0], [0,1,1,0,0], [0,0,1,0,0], [0,0,1,0,0], [0,0,1,0,0], [0,1,1,1,0], [0,0,0,0,0]],
            '2': [[0,1,1,1,0], [1,0,0,0,1], [0,0,0,1,0], [0,0,1,0,0], [0,1,0,0,0], [1,1,1,1,1], [0,0,0,0,0]],
            '3': [[1,1,1,1,0], [0,0,0,0,1], [0,1,1,1,0], [0,0,0,0,1], [0,0,0,0,1], [1,1,1,1,0], [0,0,0,0,0]],
            '4': [[1,0,0,1,0], [1,0,0,1,0], [1,0,0,1,0], [1,1,1,1,1], [0,0,0,1,0], [0,0,0,1,0], [0,0,0,0,0]],
            '5': [[1,1,1,1,1], [1,0,0,0,0], [1,1,1,1,0], [0,0,0,0,1], [0,0,0,0,1], [1,1,1,1,0], [0,0,0,0,0]],
            '+': [[0,0,0,0,0], [0,0,1,0,0], [0,1,1,1,0], [0,0,1,0,0], [0,0,0,0,0], [0,0,0,0,0], [0,0,0,0,0]],
            '-': [[0,0,0,0,0], [0,0,0,0,0], [0,1,1,1,0], [0,0,0,0,0], [0,0,0,0,0], [0,0,0,0,0], [0,0,0,0,0]],
            's': [[0,0,0,0,0], [0,1,1,1,0], [1,0,0,0,0], [0,1,1,0,0], [0,0,0,1,0], [1,1,1,0,0], [0,0,0,0,0]],
            'm': [[0,0,0,0,0], [1,1,0,1,0], [1,0,1,0,1], [1,0,1,0,1], [1,0,1,0,1], [1,0,1,0,1], [0,0,0,0,0]],
            'X': [[1,0,0,0,1], [0,1,0,1,0], [0,0,1,0,0], [0,0,1,0,0], [0,1,0,1,0], [1,0,0,0,1], [0,0,0,0,0]],
            ' ': [[0,0,0,0,0], [0,0,0,0,0], [0,0,0,0,0], [0,0,0,0,0], [0,0,0,0,0], [0,0,0,0,0], [0,0,0,0,0]],
            ':': [[0,0,0,0,0], [0,0,1,0,0], [0,0,0,0,0], [0,0,1,0,0], [0,0,0,0,0], [0,0,0,0,0], [0,0,0,0,0]],
        }

        char_x = x
        for char in text.upper():
            if char in font:
                char_pattern = font[char]
                for row_idx, row in enumerate(char_pattern):
                    for col_idx, pixel in enumerate(row):
                        if pixel:
                            self.pixel(char_x + col_idx, y + row_idx, color)
                char_x += 6  # 5px glyph + 1px spacing
            else:
                char_x += 6  # fallback for unsupported characters

    def draw_simple_text_2x(self, x, y, text, color):
        """Draws text using the same 5x7 font as draw_simple_text, at 2x size"""
        font = {
            'A': [[0,1,1,1,0], [1,0,0,0,1], [1,0,0,0,1], [1,1,1,1,1], [1,0,0,0,1], [1,0,0,0,1], [0,0,0,0,0]],
            'B': [[1,1,1,1,0], [1,0,0,0,1], [1,1,1,1,0], [1,0,0,0,1], [1,0,0,0,1], [1,1,1,1,0], [0,0,0,0,0]],
            'C': [[0,1,1,1,0], [1,0,0,0,1], [1,0,0,0,0], [1,0,0,0,0], [1,0,0,0,1], [0,1,1,1,0], [0,0,0,0,0]],
            'D': [[1,1,1,1,0], [1,0,0,0,1], [1,0,0,0,1], [1,0,0,0,1], [1,0,0,0,1], [1,1,1,1,0], [0,0,0,0,0]],
            'E': [[1,1,1,1,1], [1,0,0,0,0], [1,1,1,1,0], [1,0,0,0,0], [1,0,0,0,0], [1,1,1,1,1], [0,0,0,0,0]],
            'F': [[1,1,1,1,1], [1,0,0,0,0], [1,1,1,1,0], [1,0,0,0,0], [1,0,0,0,0], [1,0,0,0,0], [0,0,0,0,0]],
            'G': [[0,1,1,1,0], [1,0,0,0,1], [1,0,0,0,0], [1,0,1,1,1], [1,0,0,0,1], [0,1,1,1,0], [0,0,0,0,0]],
            'H': [[1,0,0,0,1], [1,0,0,0,1], [1,1,1,1,1], [1,0,0,0,1], [1,0,0,0,1], [1,0,0,0,1], [0,0,0,0,0]],
            'I': [[0,1,1,1,0], [0,0,1,0,0], [0,0,1,0,0], [0,0,1,0,0], [0,0,1,0,0], [0,1,1,1,0], [0,0,0,0,0]],
            'K': [[1,0,0,0,1], [1,0,0,1,0], [1,0,1,0,0], [1,1,0,0,0], [1,0,1,0,0], [1,0,0,1,0], [0,0,0,0,0]],
            'L': [[1,0,0,0,0], [1,0,0,0,0], [1,0,0,0,0], [1,0,0,0,0], [1,0,0,0,0], [1,1,1,1,1], [0,0,0,0,0]],
            'M': [[1,0,0,0,1], [1,1,0,1,1], [1,0,1,0,1], [1,0,0,0,1], [1,0,0,0,1], [1,0,0,0,1], [0,0,0,0,0]],
            'N': [[1,0,0,0,1], [1,1,0,0,1], [1,0,1,0,1], [1,0,0,1,1], [1,0,0,0,1], [1,0,0,0,1], [0,0,0,0,0]],
            'O': [[0,1,1,1,0], [1,0,0,0,1], [1,0,0,0,1], [1,0,0,0,1], [1,0,0,0,1], [0,1,1,1,0], [0,0,0,0,0]],
            'P': [[1,1,1,1,0], [1,0,0,0,1], [1,1,1,1,0], [1,0,0,0,0], [1,0,0,0,0], [1,0,0,0,0], [0,0,0,0,0]],
            'R': [[1,1,1,1,0], [1,0,0,0,1], [1,1,1,1,0], [1,0,1,0,0], [1,0,0,1,0], [1,0,0,0,1], [0,0,0,0,0]],
            'S': [[0,1,1,1,1], [1,0,0,0,0], [0,1,1,1,0], [0,0,0,0,1], [0,0,0,0,1], [1,1,1,1,0], [0,0,0,0,0]],
            'T': [[1,1,1,1,1], [0,0,1,0,0], [0,0,1,0,0], [0,0,1,0,0], [0,0,1,0,0], [0,0,1,0,0], [0,0,0,0,0]],
            'U': [[1,0,0,0,1], [1,0,0,0,1], [1,0,0,0,1], [1,0,0,0,1], [1,0,0,0,1], [0,1,1,1,0], [0,0,0,0,0]],
            'V': [[1,0,0,0,1], [1,0,0,0,1], [1,0,0,0,1], [1,0,0,0,1], [0,1,0,1,0], [0,0,1,0,0], [0,0,0,0,0]],
            'Y': [[1,0,0,0,1], [1,0,0,0,1], [0,1,0,1,0], [0,0,1,0,0], [0,0,1,0,0], [0,0,1,0,0], [0,0,0,0,0]],
            '0': [[0,1,1,1,0], [1,0,0,0,1], [1,0,0,0,1], [1,0,0,0,1], [1,0,0,0,1], [0,1,1,1,0], [0,0,0,0,0]],
            '1': [[0,0,1,0,0], [0,1,1,0,0], [0,0,1,0,0], [0,0,1,0,0], [0,0,1,0,0], [0,1,1,1,0], [0,0,0,0,0]],
            '2': [[0,1,1,1,0], [1,0,0,0,1], [0,0,0,1,0], [0,0,1,0,0], [0,1,0,0,0], [1,1,1,1,1], [0,0,0,0,0]],
            '3': [[1,1,1,1,0], [0,0,0,0,1], [0,1,1,1,0], [0,0,0,0,1], [0,0,0,0,1], [1,1,1,1,0], [0,0,0,0,0]],
            '4': [[1,0,0,1,0], [1,0,0,1,0], [1,0,0,1,0], [1,1,1,1,1], [0,0,0,1,0], [0,0,0,1,0], [0,0,0,0,0]],
            '5': [[1,1,1,1,1], [1,0,0,0,0], [1,1,1,1,0], [0,0,0,0,1], [0,0,0,0,1], [1,1,1,1,0], [0,0,0,0,0]],
            '+': [[0,0,0,0,0], [0,0,1,0,0], [0,1,1,1,0], [0,0,1,0,0], [0,0,0,0,0], [0,0,0,0,0], [0,0,0,0,0]],
            '-': [[0,0,0,0,0], [0,0,0,0,0], [0,1,1,1,0], [0,0,0,0,0], [0,0,0,0,0], [0,0,0,0,0], [0,0,0,0,0]],
            's': [[0,0,0,0,0], [0,1,1,1,0], [1,0,0,0,0], [0,1,1,0,0], [0,0,0,1,0], [1,1,1,0,0], [0,0,0,0,0]],
            'm': [[0,0,0,0,0], [1,1,0,1,0], [1,0,1,0,1], [1,0,1,0,1], [1,0,1,0,1], [1,0,1,0,1], [0,0,0,0,0]],
            'X': [[1,0,0,0,1], [0,1,0,1,0], [0,0,1,0,0], [0,0,1,0,0], [0,1,0,1,0], [1,0,0,0,1], [0,0,0,0,0]],
            ' ': [[0,0,0,0,0], [0,0,0,0,0], [0,0,0,0,0], [0,0,0,0,0], [0,0,0,0,0], [0,0,0,0,0], [0,0,0,0,0]],
            ':': [[0,0,0,0,0], [0,0,1,0,0], [0,0,0,0,0], [0,0,1,0,0], [0,0,0,0,0], [0,0,0,0,0], [0,0,0,0,0]],
        }

        char_x = x
        for char in text.upper():
            if char in font:
                char_pattern = font[char]
                for row_idx, row in enumerate(char_pattern):
                    for col_idx, pixel in enumerate(row):
                        if pixel:
                            for dx in range(2):
                                for dy in range(2):
                                    self.pixel(char_x + col_idx*2 + dx, y + row_idx*2 + dy, color)
                char_x += 12  # (5px glyph + 1px spacing) * 2
            else:
                char_x += 12  # fallback for unsupported characters

    def update_sensor_data(self):
        """Refreshes sensor data, combining real readings with simulated fallbacks"""

        light_value, light_voltage, light_raw = self.read_light_sensor()
        real_temp, real_humidity = self.read_temp_humidity_sensor()
        motion_detected = self.read_motion_sensor()  # reward/punishment handling happens inside

        values_changed = False

        # Light value change tolerance: 5 lux
        if abs(light_value - self.last_light_value) > 5:
            self.data_needs_update = True
            values_changed = True
            print(f"Light value changed: {self.last_light_value} -> {light_value}")

        if real_temp is not None:
            if abs(real_temp - self.sensor_data['temperature']) > 0.1:
                self.sensor_data['temperature'] = real_temp
                values_changed = True
        else:
            # Simulate temperature drift when the sensor is unavailable
            self.sensor_data['temperature'] += random.uniform(-0.5, 0.5)
            self.sensor_data['temperature'] = max(15, min(35, self.sensor_data['temperature']))

        if real_humidity is not None:
            if abs(real_humidity - self.sensor_data['humidity']) > 1:
                self.sensor_data['humidity'] = real_humidity
                values_changed = True
        else:
            # Simulate humidity drift when the sensor is unavailable
            self.sensor_data['humidity'] += random.uniform(-2, 2)
            self.sensor_data['humidity'] = max(30, min(90, self.sensor_data['humidity']))

        if (abs(self.sensor_data['temperature'] - self.last_displayed_values.get('temperature', 0)) > 0.1 or
            abs(self.sensor_data['humidity'] - self.last_displayed_values.get('humidity', 0)) > 1):
            self.data_needs_update = True

        self.sensor_data['light'] = light_value
        self.sensor_data['light_voltage'] = light_voltage
        self.sensor_data['light_raw'] = light_raw
        self.last_light_value = light_value

        print(f"Sensors - Light: {light_value} lux ({light_voltage:.2f}V), Temp: {self.sensor_data['temperature']:.1f}C, Humidity: {self.sensor_data['humidity']:.1f}%")

        # Plant health score from current sensor readings
        health = 100
        if self.sensor_data['temperature'] < 18 or self.sensor_data['temperature'] > 28:
            health -= 15
        if light_value < 300:
            health -= 20
        if self.sensor_data['humidity'] < 40 or self.sensor_data['humidity'] > 80:
            health -= 15

        self.sensor_data['plant_health'] = max(0, min(100, health))

    def handle_touch(self, x, y):
        """Handles a touch event based on the current screen"""
        print(f"Touch at: {x}, {y} on screen {self.current_screen}")

        old_screen = self.current_screen
        self.manual_mode = True
        self.last_touch_time = time.ticks_ms()

        # Bottom navigation bar
        nav_y = self.height - 40
        if y >= nav_y:
            button_width = self.width // 2
            if x < button_width:  # Dashboard button
                self.current_screen = 0
            else:  # Settings button
                self.current_screen = 2
        else:
            if self.current_screen == 0:  # Main screen
                if 20 <= y <= 100:  # first widget row
                    if 10 <= x <= 100:      # temperature widget
                        self.current_screen = 1
                    elif 110 <= x <= 200:   # humidity widget
                        self.current_screen = 1
                    elif 210 <= x <= 300:   # soil widget
                        self.current_screen = 1
                elif 110 <= y <= 190:  # second widget row
                    if 10 <= x <= 100:      # light widget
                        self.current_screen = 1
                    elif 110 <= x <= 300:   # plant health widget
                        self.current_screen = 1

            elif self.current_screen == 1:  # Detail screen
                # Tapping anywhere except the nav bar goes back to the dashboard
                self.current_screen = 0

            elif self.current_screen == 2:  # Settings screen
                settings_y = 50
                fine_y = settings_y + 50
                preset_y = fine_y + 40

                if settings_y <= y <= settings_y + 40:
                    if 20 <= x <= 80:  # -10s
                        self.motion_timeout_seconds = max(5, self.motion_timeout_seconds - 10)
                        self.motion_timeout = self.motion_timeout_seconds * 1000
                        print(f"Motion timeout set to {self.motion_timeout_seconds}s")
                        self.screen_needs_redraw = True
                    elif 240 <= x <= 300:  # +10s
                        self.motion_timeout_seconds = min(300, self.motion_timeout_seconds + 10)
                        self.motion_timeout = self.motion_timeout_seconds * 1000
                        print(f"Motion timeout set to {self.motion_timeout_seconds}s")
                        self.screen_needs_redraw = True

                elif fine_y <= y <= fine_y + 30:
                    if 50 <= x <= 100:  # -5s
                        self.motion_timeout_seconds = max(5, self.motion_timeout_seconds - 5)
                        self.motion_timeout = self.motion_timeout_seconds * 1000
                        print(f"Motion timeout set to {self.motion_timeout_seconds}s")
                        self.screen_needs_redraw = True
                    elif 220 <= x <= 270:  # +5s
                        self.motion_timeout_seconds = min(300, self.motion_timeout_seconds + 5)
                        self.motion_timeout = self.motion_timeout_seconds * 1000
                        print(f"Motion timeout set to {self.motion_timeout_seconds}s")
                        self.screen_needs_redraw = True

                elif preset_y <= y <= preset_y + 25:
                    presets = [15, 30, 60, 120]
                    for i, preset in enumerate(presets):
                        button_x = 20 + i * 70
                        if button_x <= x <= button_x + 60:
                            self.motion_timeout_seconds = preset
                            self.motion_timeout = preset * 1000
                            print(f"Motion timeout preset set to {preset}s")
                            self.screen_needs_redraw = True
                            break

        if old_screen != self.current_screen:
            self.screen_needs_redraw = True

    def check_auto_mode_timeout(self):
        """Switches back to auto mode after a period of no touch input"""
        if self.manual_mode:
            current_time = time.ticks_ms()
            if time.ticks_diff(current_time, self.last_touch_time) > 60000:  # 1 minute
                self.manual_mode = False
                print("Back to auto mode")

    def run_ui(self):
        """Main UI loop with touch support"""
        screen_count = 2  # dashboard (0) and settings (2) only
        last_screen_change = time.ticks_ms()
        screen_duration = 180000  # 3 minutes per screen, auto mode only
        last_touch_pos = None

        try:
            while True:
                current_time = time.ticks_ms()

                if self.touch:
                    touch_pos = self.touch.get_touch()
                    if touch_pos and touch_pos != last_touch_pos:
                        x, y = touch_pos
                        self.handle_touch(x, y)
                        last_touch_pos = touch_pos
                    elif not touch_pos:
                        last_touch_pos = None

                self.check_auto_mode_timeout()

                # Refresh sensor data every 5 seconds
                if time.ticks_diff(current_time, self.last_update) > 5000:
                    self.update_sensor_data()
                    self.last_update = current_time

                # Only fully redraw when needed
                if self.screen_needs_redraw or self.last_drawn_screen != self.current_screen:
                    if self.current_screen == 0:
                        self.show_main_screen()
                    elif self.current_screen == 1:
                        self.show_detail_screen()
                    else:
                        self.show_settings_screen()

                    for key in self.last_displayed_values:
                        self.last_displayed_values[key] = self.sensor_data.get(key, 0)

                    self.last_drawn_screen = self.current_screen
                    self.screen_needs_redraw = False
                    self.data_needs_update = False
                    print(f"Screen {self.current_screen} fully redrawn")

                elif self.data_needs_update:
                    self.update_display_values_only()
                    self.data_needs_update = False
                    print("Sensor values updated (no full redraw)")

                # Auto-switch screens only in auto mode
                if not self.manual_mode and time.ticks_diff(current_time, last_screen_change) > screen_duration:
                    old_screen = self.current_screen
                    if self.current_screen == 0:
                        self.current_screen = 2
                    else:
                        self.current_screen = 0
                    last_screen_change = current_time
                    print(f"Auto-switched to screen {self.current_screen}")
                    if old_screen != self.current_screen:
                        self.screen_needs_redraw = True

                time.sleep(0.2)

        except KeyboardInterrupt:
            print("Stopping UI...")
            self.cleanup_audio()
            raise
        except Exception as e:
            print(f"UI error: {e}")
            self.cleanup_audio()
            raise

    def update_display_values_only(self):
        """Updates only the numeric values on screen, without a full redraw"""
        if self.current_screen == 0:  # Main screen
            y_start = 20  # must match show_main_screen()

            if abs(self.sensor_data['temperature'] - self.last_displayed_values['temperature']) > 0.1:
                self.fill_rect(20, y_start + 45, 65, 30, GRAY_LIGHT)
                self.draw_number(20, y_start + 45, self.sensor_data['temperature'], 2, ORANGE)
                self.last_displayed_values['temperature'] = self.sensor_data['temperature']

            if abs(self.sensor_data['humidity'] - self.last_displayed_values['humidity']) > 1:
                self.fill_rect(20, y_start + 135, 65, 30, GRAY_LIGHT)
                self.draw_number(20, y_start + 135, self.sensor_data['humidity'], 2, BLUE_LIGHT)
                self.last_displayed_values['humidity'] = self.sensor_data['humidity']

            if abs(self.sensor_data['light'] - self.last_displayed_values['light']) > 5:
                light_value = int(self.sensor_data['light'])
                light_color = self.get_light_quality_color(light_value)
                light_description = self.get_light_quality_description(light_value)

                self.fill_rect(110, y_start, 200, 80, GRAY_LIGHT)  # clear the whole light widget
                self.draw_icon_sun(120, y_start + 10, 60, light_color)

                text_x = 190
                text_y = y_start + 20

                if len(light_description) > 10:
                    words = light_description.split()
                    if len(words) >= 2:
                        self.draw_simple_text_2x(text_x, text_y, words[0], light_color)
                        self.draw_simple_text_2x(text_x, text_y + 20, words[1], light_color)
                    else:
                        short_desc = light_description[:10]
                        self.draw_simple_text_2x(text_x, text_y, short_desc, light_color)
                else:
                    self.draw_simple_text_2x(text_x, text_y, light_description, light_color)

                self.last_displayed_values['light'] = light_value

            if abs(self.sensor_data['plant_health'] - self.last_displayed_values['plant_health']) > 1:
                health = self.sensor_data['plant_health']
                if health > 80:
                    status_color = GREEN_LIGHT
                elif health > 60:
                    status_color = YELLOW
                else:
                    status_color = RED
                self.draw_progress_bar(120, y_start + 110, 180, 25, health, 100, GRAY_DARK, status_color)
                self.last_displayed_values['plant_health'] = health

        elif self.current_screen == 1:  # Detail screen
            y = 20  # must match show_detail_screen()

            if abs(self.sensor_data['temperature'] - self.last_displayed_values['temperature']) > 0.1:
                self.fill_rect(200, y + 5, 80, 30, GRAY_LIGHT)
                temp_str = f"{self.sensor_data['temperature']:.1f}"
                self.draw_number(200, y + 5, float(temp_str), 3, ORANGE)
                self.last_displayed_values['temperature'] = self.sensor_data['temperature']

            y += 50

            if abs(self.sensor_data['light'] - self.last_displayed_values['light']) > 5:
                light_value = self.sensor_data['light']
                light_color = self.get_light_quality_color(light_value)
                light_description = self.get_light_quality_description(light_value)

                self.draw_progress_bar(70, y + 10, 150, 20, light_value, 1000, GRAY_DARK, light_color)
                self.fill_rect(230, y + 15, 75, 15, GRAY_LIGHT)
                self.draw_simple_text(230, y + 15, light_description, light_color)
                self.last_displayed_values['light'] = light_value

    def draw_bottom_navigation_bar(self):
        """Draws the touch navigation bar at the bottom of the screen"""
        nav_height = 40
        nav_y = self.height - nav_height

        self.fill_rect(0, nav_y, self.width, nav_height, GRAY_DARK)

        button_width = self.width // 2

        # Dashboard button (left)
        dashboard_active = self.current_screen == 0
        dashboard_color = GREEN_LIGHT if dashboard_active else GRAY_LIGHT
        self.draw_rounded_rect(5, nav_y + 5, button_width - 10, nav_height - 10, 8, dashboard_color)

        icon_start_x = 15
        text_start_x = icon_start_x + 30
        center_y = nav_y + 15

        # Dashboard icon: simple 2x2 grid
        icon_x = icon_start_x
        icon_y = center_y - 8
        for i in range(2):
            for j in range(2):
                rect_x = icon_x + i * 8
                rect_y = icon_y + j * 8
                icon_color = BLACK if dashboard_active else WHITE
                self.fill_rect(rect_x, rect_y, 6, 6, icon_color)

        text_color = BLACK if dashboard_active else WHITE
        self.draw_simple_text(text_start_x, center_y - 3, "Dashboard", text_color)

        # Settings button (right)
        settings_active = self.current_screen == 2
        settings_color = ORANGE if settings_active else GRAY_LIGHT
        self.draw_rounded_rect(button_width + 5, nav_y + 5, button_width - 10, nav_height - 10, 8, settings_color)

        settings_icon_start_x = button_width + 15
        settings_text_start_x = settings_icon_start_x + 25

        # Settings icon: simplified gear
        settings_icon_x = settings_icon_start_x
        settings_icon_y = center_y - 6
        icon_color = BLACK if settings_active else WHITE
        self.draw_circle(settings_icon_x + 6, settings_icon_y + 6, 6, icon_color)
        self.fill_rect(settings_icon_x + 4, settings_icon_y + 4, 4, 4, GRAY_DARK)

        text_color = BLACK if settings_active else WHITE
        self.draw_simple_text(settings_text_start_x, center_y - 3, "Settings", text_color)

    def get_light_quality_description(self, light_value):
        """Maps a light value to a qualitative label"""
        if light_value >= 800:
            return "EXCELLENT"
        elif light_value >= 600:
            return "VERY GOOD"
        elif light_value >= 400:
            return "GOOD"
        elif light_value >= 200:
            return "POOR"
        else:
            return "VERY POOR"

    def get_light_quality_color(self, light_value):
        """Maps a light value to a display color"""
        if light_value >= 800:
            return GREEN_LIGHT
        elif light_value >= 600:
            return YELLOW
        elif light_value >= 400:
            return ORANGE
        elif light_value >= 200:
            return RED
        else:
            return GRAY_DARK

def main():
    print("=== Smart Plant UI with Touch ===")

    # Display pins
    dc_pin = machine.Pin(17, machine.Pin.OUT)
    reset_pin = machine.Pin(20, machine.Pin.OUT)
    cs_pin = machine.Pin(21, machine.Pin.OUT)

    # Touch pins
    touch_cs_pin = machine.Pin(1, machine.Pin.OUT)   # T_CS
    touch_irq_pin = machine.Pin(6, machine.Pin.IN)   # T_IRQ

    # Hardware SPI0 for the display
    display_spi = machine.SPI(0,
                      baudrate=20000000,
                      polarity=0,
                      phase=0)

    # Software (bit-banged) SPI for touch
    touch_sck = machine.Pin(2, machine.Pin.OUT)   # T_CLK = GP2
    touch_mosi = machine.Pin(3, machine.Pin.OUT)  # T_DIN = GP3
    touch_miso = machine.Pin(5, machine.Pin.IN)   # T_DO = GP5

    touch_spi = machine.SoftSPI(
        baudrate=100000,  # slower for a more stable touch link
        polarity=0,
        phase=0,
        sck=touch_sck,
        mosi=touch_mosi,
        miso=touch_miso
    )

    touch = TouchController(touch_spi, touch_cs_pin, touch_irq_pin)

    plant_ui = SmartPlantDisplay(display_spi, dc_pin, reset_pin, cs_pin, touch)
    plant_ui.init()

    print("Touch controller configured:")
    print("  T_CS: GP1")
    print("  T_IRQ: GP6")
    print("  T_CLK: GP2 (software SPI)")
    print("  T_DIN: GP3 (software SPI)")
    print("  T_DO: GP5 (software SPI)")

    print("Sensors configured:")
    print("  LDR: GP28 (ADC2) - light sensor")
    print("  DHT11: GP27 - temperature and humidity")
    print(f"  Motion: GP26 - active, {plant_ui.motion_timeout_seconds}s timeout (adjustable)")

    print("Audio system configured:")
    print("  I2S BCLK: GP10")
    print("  I2S WS/LRC: GP11")
    print("  I2S DIN: GP12")
    print(f"  Punishment: 5s sine wave (3000 Hz) after {plant_ui.motion_timeout_seconds}s without motion")
    print("  Reward: C major melody (2s) on motion detection")

    print("Starting plant pot UI with touch and live sensors...")
    print("Tap the display for manual control!")
    print(f"Motion sensor: reward on watering, punishment after {plant_ui.motion_timeout_seconds}s without motion")
    print("Settings tab: motion timeout adjustable (5-300 seconds)")

    try:
        plant_ui.run_ui()
    except KeyboardInterrupt:
        print("UI stopped")
        plant_ui.cleanup_audio()
        plant_ui.fill(BLACK)


if __name__ == "__main__":
    main()
