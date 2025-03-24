import osmnx as ox
import pygame
import networkx as nx
from dataclasses import dataclass
import logging
import os
import time
import math
import contextily as ctx
import matplotlib.pyplot as plt
import io
from PIL import Image
import hashlib
import requests

# Налаштування логування
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s - %(levelname)s - %(message)s",
    handlers=[logging.FileHandler("game_log.txt", mode="w"), logging.StreamHandler()]
)
logger = logging.getLogger(__name__)

# Ініціалізація Pygame
pygame.init()
WIDTH, HEIGHT = 800, 600
screen = pygame.display.set_mode((WIDTH, HEIGHT))
pygame.display.set_caption("Combrig")
logger.info("Pygame initialized successfully")

font = pygame.font.SysFont("Arial", 20)
small_font = pygame.font.SysFont("Arial", 16)
zoom_font = pygame.font.SysFont("Arial", 20, bold=True)
label_font = pygame.font.SysFont("Arial", 14)

# Константи гри
ORGANIZATION_INCREASE_RATE = 0.0
ORGANIZATION_DECREASE_RATE = 0.0
BASE_INFLUENCE_RADIUS = 5000
CAMERA_SPEED = 10
ZOOM_FACTOR = 1.1
MIN_ZOOM = 10
MAX_ZOOM = 19
DARK_GRAY = (40, 40, 40)
LIGHT_GRAY = (100, 100, 100)
UI_BLUE = (70, 130, 180)
UI_RED = (180, 70, 70)
TOP_PANEL_HEIGHT = 30
SIDEBAR_WIDTH = 250
TILE_SIZE = 256  # Розмір тайлу OSM (256x256 пікселів)

# Завантаження зображень
def load_images():
    images = {}
    try:
        if not os.path.exists("assets"):
            os.makedirs("assets")
            logger.info("Created assets directory")
        if os.path.exists("assets/infantry_brigade.png"):
            images["infantry_brigade"] = pygame.image.load("assets/infantry_brigade.png").convert_alpha()
            logger.info("Loaded infantry_brigade.png")
        else:
            dummy_surface = pygame.Surface((32, 32), pygame.SRCALPHA)
            pygame.draw.rect(dummy_surface, (0, 0, 255), (4, 4, 24, 24), 2)
            pygame.draw.line(dummy_surface, (0, 0, 255), (4, 4), (28, 28), 2)
            pygame.draw.line(dummy_surface, (0, 0, 255), (4, 28), (28, 4), 2)
            images["infantry_brigade"] = dummy_surface
            logger.warning("infantry_brigade.png not found, using HoI-style placeholder")
        
        images["infantry_brigade_moving"] = []
        for i in range(4):
            frame = images["infantry_brigade"].copy()
            offset = i * 2
            pygame.draw.line(frame, (255, 255, 0), (8 + offset, 28), (24 + offset, 28), 2)
            images["infantry_brigade_moving"].append(frame)
    except Exception as e:
        logger.error(f"Error loading images: {e}")
        dummy_surface = pygame.Surface((32, 32), pygame.SRCALPHA)
        pygame.draw.rect(dummy_surface, (0, 0, 255), (4, 4, 24, 24), 2)
        pygame.draw.line(dummy_surface, (0, 0, 255), (4, 4), (28, 28), 2)
        pygame.draw.line(dummy_surface, (0, 0, 255), (4, 28), (28, 4), 2)
        images["infantry_brigade"] = dummy_surface
        images["infantry_brigade_moving"] = [dummy_surface] * 4
    return images

unit_images = load_images()

class GameState:
    MAIN_MENU = 0
    PLAYING = 1
    MISSION_BRIEFING = 2
    GAME_OVER = 3

@dataclass
class Unit:
    name: str
    speed: float
    position: tuple[float, float]
    organization: float = 100.0
    selected: bool = False
    path: list = None
    current_position: tuple[float, float] = None
    target_position: tuple[float, float] = None
    interpolation_progress: float = 1.0
    image_key: str = "infantry_brigade"
    
    def is_moving(self):
        return self.path and len(self.path) > 0
    
    def move(self, graph, dt):
        if self.path and len(self.path) > 0:
            if self.interpolation_progress >= 1.0:
                next_node = self.path[0]
                self.current_position = self.position
                self.target_position = (graph.nodes[next_node]["y"], graph.nodes[next_node]["x"])
                self.interpolation_progress = 0.0
                self.path.pop(0)
            if self.current_position and self.target_position:
                self.interpolation_progress += self.speed * dt / 1000.0
                self.interpolation_progress = min(1.0, self.interpolation_progress)
                lat = self.current_position[0] + (self.target_position[0] - self.current_position[0]) * self.interpolation_progress
                lon = self.current_position[1] + (self.target_position[1] - self.current_position[1]) * self.interpolation_progress
                self.position = (lat, lon)

class Game:
    def __init__(self):
        logger.info("Starting map loading for Combrig...")
        cache_folder = './cache'
        if not os.path.exists(cache_folder):
            os.makedirs(cache_folder)
        self.tiles_cache_folder = f'{cache_folder}/tiles'
        if not os.path.exists(self.tiles_cache_folder):
            os.makedirs(self.tiles_cache_folder)
            logger.info("Created tiles cache directory")

        self.load_highways_map()
        self.classify_roads()
        self.load_labels_data()
        
        # Початковий центр карти (Суми, Україна)
        try:
            start_point = ox.geocode("Sumy, Ukraine")
        except Exception as e:
            logger.error(f"Geocoding failed: {e}")
            start_point = (50.9216, 34.8003)
        
        self.center_lat, self.center_lon = start_point
        self.zoom = 14  # Початковий рівень масштабування (аналогічно OSM)

        self.base_node = ox.distance.nearest_nodes(self.graph, start_point[1], start_point[0])
        self.base_position = (self.graph.nodes[self.base_node]["y"], self.graph.nodes[self.base_node]["x"])
        logger.info(f"Base set at {self.base_position}")
        
        self.units = [
            Unit("Infantry Brigade 1", speed=2.0, position=self.base_position),
            Unit("Infantry Brigade 2", speed=1.5, position=self.base_position),
            Unit("Infantry Brigade 3", speed=1.8, position=self.base_position)
        ]
        self.distribute_units()
        
        self.path_cache = {}
        self.state = GameState.PLAYING
        
        self.draw_all_roads = False
        self.road_buffer = 200
        
        self.zoom_in_button = pygame.Rect(WIDTH - 30, HEIGHT // 2 - 25, 20, 20)
        self.zoom_out_button = pygame.Rect(WIDTH - 30, HEIGHT // 2, 20, 20)
        
        self.dragging = False
        self.drag_start = None
        self.drag_current = None
        
        self.selection_box_active = False
        self.selection_start = None
        self.selection_current = None
        
        self.show_sidebar = True
        self.sidebar_rect = pygame.Rect(0, TOP_PANEL_HEIGHT, SIDEBAR_WIDTH, HEIGHT - TOP_PANEL_HEIGHT)
        self.sidebar_scroll = 0
        
        self.resources = {
            "manpower": 1200,
            "supplies": 75,
            "fuel": 94,
            "equipment": 5.95,
            "divisions": 100,
            "efficiency": 2.4,
            "ships": 378
        }
        self.supply_lines = []

        self.tiles = {}  # Кеш тайлів у пам’яті

    def latlon_to_tile(self, lat, lon, zoom):
        """Перетворює географічні координати в номери тайлів OSM"""
        lat_rad = math.radians(lat)
        n = 2.0 ** zoom
        x_tile = int((lon + 180.0) / 360.0 * n)
        y_tile = int((1.0 - math.asinh(math.tan(lat_rad)) / math.pi) / 2.0 * n)
        return x_tile, y_tile

    def tile_to_latlon(self, x_tile, y_tile, zoom):
        """Перетворює номери тайлів OSM у географічні координати (верхній лівий кут тайлу)"""
        n = 2.0 ** zoom
        lon_deg = x_tile / n * 360.0 - 180.0
        lat_rad = math.atan(math.sinh(math.pi * (1 - 2 * y_tile / n)))
        lat_deg = math.degrees(lat_rad)
        return lat_deg, lon_deg

    def world_to_screen(self, geo_coords):
        """Перетворює географічні координати (lat, lon) у координати екрану (x, y)"""
        lat, lon = geo_coords
        # Обчислюємо позицію в системі Меркатора
        lat_rad = math.radians(lat)
        merc_x = lon
        merc_y = math.log(math.tan(math.pi / 4 + lat_rad / 2))
        
        center_lat_rad = math.radians(self.center_lat)
        center_merc_x = self.center_lon
        center_merc_y = math.log(math.tan(math.pi / 4 + center_lat_rad / 2))
        
        # Масштабування
        n = 2 ** self.zoom
        scale = n * TILE_SIZE / 360.0  # Пікселів на градус
        
        screen_x = (merc_x - center_merc_x) * scale + WIDTH / 2
        screen_y = (center_merc_y - merc_y) * scale + HEIGHT / 2
        return (screen_x, screen_y)

    def screen_to_world(self, screen_coords):
        """Перетворює координати екрану (x, y) у географічні координати (lat, lon)"""
        x, y = screen_coords
        center_lat_rad = math.radians(self.center_lat)
        center_merc_x = self.center_lon
        center_merc_y = math.log(math.tan(math.pi / 4 + center_lat_rad / 2))
        
        n = 2 ** self.zoom
        scale = n * TILE_SIZE / 360.0
        
        merc_x = (x - WIDTH / 2) / scale + center_merc_x
        merc_y = center_merc_y - (y - HEIGHT / 2) / scale
        
        lon = merc_x
        lat_rad = 2 * (math.atan(math.exp(merc_y)) - math.pi / 4)
        lat = math.degrees(lat_rad)
        return (lat, lon)

    def load_highways_map(self):
        cache_folder = './cache'
        try:
            if os.path.exists(f'{cache_folder}/sumy_map_highways.graphml'):
                self.graph = ox.load_graphml(f'{cache_folder}/sumy_map_highways.graphml')
                logger.info("Highways map loaded from cache")
            else:
                self.graph = ox.graph_from_place("Sumy, Ukraine", network_type="drive", 
                                                custom_filter='["highway"~"motorway|trunk|primary|secondary|tertiary|residential"]')
                ox.save_graphml(self.graph, f'{cache_folder}/sumy_map_highways.graphml')
                logger.info("Highways map loaded from OSM and cached")
        except Exception as e:
            logger.error(f"Error loading highways map: {e}")
            self.graph = nx.grid_graph(dim=[10, 10])
            mapping = {node: i for i, node in enumerate(self.graph.nodes())}
            self.graph = nx.relabel_nodes(self.graph, mapping)
            for node in self.graph.nodes():
                self.graph.nodes[node]['x'] = float(node % 10) * 0.001
                self.graph.nodes[node]['y'] = float(node // 10) * 0.001
            logger.info("Created fallback grid graph")

    def classify_roads(self):
        self.road_types = {
            "motorway": [], "trunk": [], "primary": [], "secondary": [],
            "tertiary": [], "residential": [], "other": []
        }
        for u, v, data in self.graph.edges(data=True):
            road_type = "other"
            if "highway" in data:
                if isinstance(data["highway"], str) and data["highway"] in self.road_types:
                    road_type = data["highway"]
                elif isinstance(data["highway"], list):
                    for h in data["highway"]:
                        if h in self.road_types:
                            road_type = h
                            break
            x1, y1 = self.graph.nodes[u]["x"], self.graph.nodes[u]["y"]
            x2, y2 = self.graph.nodes[v]["x"], self.graph.nodes[v]["y"]
            self.road_types[road_type].append((u, v, x1, y1, x2, y2))
        logger.info(f"Classified roads: {sum(len(roads) for roads in self.road_types.values())} total")

    def load_labels_data(self):
        """Завантажуємо дані про назви вулиць і міст для відображення"""
        try:
            # Завантажуємо геометрію доріг із назвами
            self.street_labels = []
            streets = ox.features_from_place("Sumy, Ukraine", tags={"highway": True})
            for _, row in streets.iterrows():
                if "name" in row and row["geometry"].type == "LineString":
                    coords = list(row["geometry"].coords)
                    mid_point = coords[len(coords) // 2]
                    self.street_labels.append({
                        "name": row["name"],
                        "position": (mid_point[1], mid_point[0])
                    })
            
            # Завантажуємо міста/селища
            self.place_labels = []
            places = ox.features_from_place("Sumy, Ukraine", tags={"place": ["city", "town", "village"]})
            for _, row in places.iterrows():
                if "name" in row and row["geometry"].type == "Point":
                    coords = (row["geometry"].y, row["geometry"].x)
                    self.place_labels.append({
                        "name": row["name"],
                        "position": coords
                    })
            logger.info(f"Loaded {len(self.street_labels)} street labels and {len(self.place_labels)} place labels")
        except Exception as e:
            logger.error(f"Error loading labels: {e}")
            self.street_labels = []
            self.place_labels = []

    def load_tile(self, x_tile, y_tile, zoom):
        """Завантажує або повертає тайл із кешу"""
        tile_key = f"{zoom}_{x_tile}_{y_tile}"
        if tile_key in self.tiles:
            return self.tiles[tile_key]
        
        cache_filename = os.path.join(self.tiles_cache_folder, f"{tile_key}.png")
        if os.path.exists(cache_filename):
            tile = pygame.image.load(cache_filename).convert_alpha()
            self.tiles[tile_key] = tile
            logger.info(f"Tile loaded from cache: {cache_filename}")
            return tile
        
        # Завантажуємо тайл із OSM
        url = f"https://tile.openstreetmap.org/{zoom}/{x_tile}/{y_tile}.png"
        try:
            response = requests.get(url, headers={"User-Agent": "Combrig/1.0"})
            if response.status_code == 200:
                image = Image.open(io.BytesIO(response.content))
                mode = image.mode
                size = image.size
                data = image.tobytes()
                tile = pygame.image.fromstring(data, size, mode).convert_alpha()
                pygame.image.save(tile, cache_filename)
                self.tiles[tile_key] = tile
                logger.info(f"Tile downloaded and cached: {cache_filename}")
                return tile
        except Exception as e:
            logger.error(f"Error downloading tile {tile_key}: {e}")
        
        # Якщо не вдалося завантажити, повертаємо порожній тайл
        tile = pygame.Surface((TILE_SIZE, TILE_SIZE))
        tile.fill((255, 255, 255))
        self.tiles[tile_key] = tile
        return tile

    def draw_map(self):
        """Відображає тайли карти OSM"""
        # Обчислюємо тайли, які потрібно відобразити
        top_left = self.screen_to_world((0, 0))
        bottom_right = self.screen_to_world((WIDTH, HEIGHT))
        
        x_tile_min, y_tile_min = self.latlon_to_tile(top_left[0], top_left[1], self.zoom)
        x_tile_max, y_tile_max = self.latlon_to_tile(bottom_right[0], bottom_right[1], self.zoom)
        
        for x_tile in range(x_tile_min, x_tile_max + 1):
            for y_tile in range(y_tile_min, y_tile_max + 1):
                tile = self.load_tile(x_tile, y_tile, self.zoom)
                tile_lat, tile_lon = self.tile_to_latlon(x_tile, y_tile, self.zoom)
                screen_x, screen_y = self.world_to_screen((tile_lat, tile_lon))
                screen.blit(tile, (int(screen_x), int(screen_y)))

    def distribute_units(self):
        logger.info("Distributing units around base...")
        nearby_nodes = list(self.graph.neighbors(self.base_node))
        if not nearby_nodes:
            logger.warning("No nearby nodes found, placing all units at base")
            return
        for i, unit in enumerate(self.units):
            node = nearby_nodes[i % len(nearby_nodes)]
            unit.position = (self.graph.nodes[node]["y"], self.graph.nodes[node]["x"])
            unit.current_position = unit.position
            unit.target_position = unit.position
            logger.info(f"{unit.name} placed at {unit.position}")

    def find_nearest_node(self, pos):
        geo_pos = self.screen_to_world(pos)
        return ox.distance.nearest_nodes(self.graph, geo_pos[1], geo_pos[0])

    def set_unit_target(self, unit, target_pos):
        try:
            start_node = ox.distance.nearest_nodes(self.graph, unit.position[1], unit.position[0])
            target_node = self.find_nearest_node(target_pos)
            
            if start_node == target_node:
                neighbors = list(self.graph.neighbors(start_node))
                if neighbors:
                    intermediate_node = neighbors[0]
                    unit.path = [intermediate_node, target_node]
                    unit.interpolation_progress = 1.0
                    logger.info(f"Path set for {unit.name} through intermediate node")
                    return
            
            if nx.has_path(self.graph, start_node, target_node):
                path_key = f"{start_node}_{target_node}"
                if path_key in self.path_cache:
                    unit.path = self.path_cache[path_key].copy()
                else:
                    unit.path = nx.astar_path(self.graph, start_node, target_node, weight="length")
                    self.path_cache[path_key] = unit.path.copy()
                unit.interpolation_progress = 1.0
                logger.info(f"Path set for {unit.name} to {target_pos}")
            else:
                logger.warning(f"No path exists for {unit.name} to {target_pos}")
                unit.path = None
        except Exception as e:
            logger.warning(f"No path found for {unit.name} to {target_pos}: {e}")
            unit.path = None

    def handle_camera_control(self):
        keys = pygame.key.get_pressed()
        if keys[pygame.K_UP]:
            new_center = self.screen_to_world((WIDTH / 2, HEIGHT / 2 - CAMERA_SPEED))
            self.center_lat, self.center_lon = new_center
        if keys[pygame.K_DOWN]:
            new_center = self.screen_to_world((WIDTH / 2, HEIGHT / 2 + CAMERA_SPEED))
            self.center_lat, self.center_lon = new_center
        if keys[pygame.K_LEFT]:
            new_center = self.screen_to_world((WIDTH / 2 - CAMERA_SPEED, HEIGHT / 2))
            self.center_lat, self.center_lon = new_center
        if keys[pygame.K_RIGHT]:
            new_center = self.screen_to_world((WIDTH / 2 + CAMERA_SPEED, HEIGHT / 2))
            self.center_lat, self.center_lon = new_center

    def handle_zoom(self, event):
        if event.type == pygame.MOUSEBUTTONDOWN:
            mouse_pos = event.pos
            old_mouse_world = self.screen_to_world(mouse_pos)
            
            if event.button == 4:  # Збільшення масштабу
                self.zoom = min(MAX_ZOOM, self.zoom + 1)
            elif event.button == 5:  # Зменшення масштабу
                self.zoom = max(MIN_ZOOM, self.zoom - 1)
            
            # Перераховуємо центр, щоб точка під курсором залишалася на місці
            new_mouse_world = self.screen_to_world(mouse_pos)
            self.center_lon += old_mouse_world[1] - new_mouse_world[1]
            self.center_lat += old_mouse_world[0] - new_mouse_world[0]

    def handle_zoom_buttons(self, mouse_pos, mouse_clicked):
        pygame.draw.rect(screen, LIGHT_GRAY, self.zoom_in_button)
        pygame.draw.rect(screen, LIGHT_GRAY, self.zoom_out_button)
        screen.blit(zoom_font.render("+", True, (255, 255, 255)), (self.zoom_in_button.x + 5, self.zoom_in_button.y + 2))
        screen.blit(zoom_font.render("−", True, (255, 255, 255)), (self.zoom_out_button.x + 5, self.zoom_out_button.y + 2))
        if mouse_clicked:
            old_mouse_world = self.screen_to_world(mouse_pos)
            
            if self.zoom_in_button.collidepoint(mouse_pos):
                self.zoom = min(MAX_ZOOM, self.zoom + 1)
                logger.info(f"Zoomed in, zoom: {self.zoom}")
            elif self.zoom_out_button.collidepoint(mouse_pos):
                self.zoom = max(MIN_ZOOM, self.zoom - 1)
                logger.info(f"Zoomed out, zoom: {self.zoom}")
            
            new_mouse_world = self.screen_to_world(mouse_pos)
            self.center_lon += old_mouse_world[1] - new_mouse_world[1]
            self.center_lat += old_mouse_world[0] - new_mouse_world[0]

    def handle_mouse_events(self, event):
        if event.type == pygame.MOUSEBUTTONDOWN:
            pos = pygame.mouse.get_pos()
            if self.show_sidebar and self.sidebar_rect.collidepoint(pos):
                self.handle_sidebar_click(pos)
                return
            if self.zoom_in_button.collidepoint(pos) or self.zoom_out_button.collidepoint(pos):
                return
            if event.button == 1:
                units_at_pos = self.get_units_at_position(pos)
                if units_at_pos:
                    if len(units_at_pos) == 1:
                        unit = units_at_pos[0]
                        unit.selected = not unit.selected
                        logger.info(f"{unit.name} selected: {unit.selected}")
                    else:
                        for unit in units_at_pos:
                            unit.selected = True
                            logger.info(f"{unit.name} selected: True")
                else:
                    self.dragging = True
                    self.drag_start = pos
                    self.drag_current = pos
                    pygame.mouse.set_cursor(pygame.SYSTEM_CURSOR_SIZEALL)
            elif event.button == 3:
                if pygame.key.get_mods() & pygame.KMOD_SHIFT:
                    for unit in self.units:
                        if unit.selected:
                            self.set_unit_target(unit, pos)
                else:
                    self.selection_box_active = True
                    self.selection_start = pos
                    self.selection_current = pos
        elif event.type == pygame.MOUSEBUTTONUP:
            if event.button == 1:
                if self.dragging:
                    self.dragging = False
                    self.drag_start = None
                    self.drag_current = None
                    pygame.mouse.set_cursor(pygame.SYSTEM_CURSOR_ARROW)
            elif event.button == 3:
                if self.selection_box_active:
                    self.selection_box_active = False
                    self.select_units_in_box(self.selection_start, self.selection_current)
                    self.selection_start = None
                    self.selection_current = None
        elif event.type == pygame.MOUSEMOTION:
            if self.selection_box_active:
                self.selection_current = event.pos
            if self.dragging:
                self.drag_current = event.pos
                dx = self.drag_current[0] - self.drag_start[0]
                dy = self.drag_current[1] - self.drag_start[1]
                new_center = self.screen_to_world((WIDTH / 2 - dx, HEIGHT / 2 - dy))
                self.center_lat, self.center_lon = new_center
                self.drag_start = self.drag_current
        elif event.type == pygame.MOUSEWHEEL:
            if self.show_sidebar and self.sidebar_rect.collidepoint(pygame.mouse.get_pos()):
                self.sidebar_scroll -= event.y * 20
                self.sidebar_scroll = max(0, self.sidebar_scroll)

    def get_units_at_position(self, pos):
        units_at_pos = []
        for unit in self.units:
            unit_x, unit_y = self.world_to_screen(unit.position)
            if ((pos[0] - unit_x) ** 2 + (pos[1] - unit_y) ** 2) ** 0.5 < 20:
                units_at_pos.append(unit)
        return units_at_pos

    def select_units_in_box(self, start_pos, end_pos):
        drag_distance = ((start_pos[0] - end_pos[0])**2 + (start_pos[1] - end_pos[1])**2)**0.5
        if drag_distance < 5:
            return
        x1, y1 = min(start_pos[0], end_pos[0]), min(start_pos[1], end_pos[1])
        x2, y2 = max(start_pos[0], end_pos[0]), max(start_pos[1], end_pos[1])
        selection_rect = pygame.Rect(x1, y1, x2 - x1, y2 - y1)
        if not pygame.key.get_mods() & pygame.KMOD_SHIFT:
            for unit in self.units:
                unit.selected = False
        for unit in self.units:
            unit_x, unit_y = self.world_to_screen(unit.position)
            if selection_rect.collidepoint(unit_x, unit_y):
                unit.selected = True
                logger.info(f"{unit.name} selected: True")

    def handle_sidebar_click(self, pos):
        icon_height = 30
        visible_height = HEIGHT - TOP_PANEL_HEIGHT
        for i, unit in enumerate(self.units):
            icon_y = TOP_PANEL_HEIGHT + 70 + i * icon_height - self.sidebar_scroll
            if icon_y < TOP_PANEL_HEIGHT or icon_y + icon_height > HEIGHT:
                continue
            icon_rect = pygame.Rect(5, icon_y, SIDEBAR_WIDTH - 10, icon_height - 2)
            if icon_rect.collidepoint(pos):
                unit.selected = not unit.selected
                logger.info(f"{unit.name} selected from sidebar: {unit.selected}")

    def draw_roads(self):
        road_styles = {
            "motorway": {"color": (255, 0, 0), "width": 4}, "trunk": {"color": (255, 97, 0), "width": 3},
            "primary": {"color": (255, 165, 0), "width": 3}, "secondary": {"color": (255, 255, 0), "width": 2},
            "tertiary": {"color": (0, 255, 0), "width": 2}, "residential": {"color": (200, 200, 200), "width": 1},
            "other": {"color": (150, 150, 150), "width": 1}
        }
        visible_road_types = ["motorway", "trunk", "primary"] if self.zoom < 12 else \
                            ["motorway", "trunk", "primary", "secondary"] if self.zoom < 14 else \
                            ["motorway", "trunk", "primary", "secondary", "tertiary", "residential"]
        for road_type in visible_road_types:
            for u, v, x1, y1, x2, y2 in self.road_types[road_type]:
                screen_x1, screen_y1 = self.world_to_screen((y1, x1))
                screen_x2, screen_y2 = self.world_to_screen((y2, x2))
                if self.draw_all_roads or (
                    (0 - self.road_buffer <= screen_x1 <= WIDTH + self.road_buffer and 
                     0 - self.road_buffer <= screen_y1 <= HEIGHT + self.road_buffer) or
                    (0 - self.road_buffer <= screen_x2 <= WIDTH + self.road_buffer and 
                     0 - self.road_buffer <= screen_y2 <= HEIGHT + self.road_buffer)):
                    pygame.draw.line(screen, road_styles[road_type]["color"], (screen_x1, screen_y1), 
                                    (screen_x2, screen_y2), road_styles[road_type]["width"])

    def draw_supply_lines(self):
        for unit in self.units:
            if unit.position != self.base_position:
                base_x, base_y = self.world_to_screen(self.base_position)
                unit_x, unit_y = self.world_to_screen(unit.position)
                dash_length = 10
                total_length = ((unit_x - base_x)**2 + (unit_y - base_y)**2)**0.5
                num_dashes = int(total_length / (dash_length * 2))
                for i in range(num_dashes):
                    start_x = base_x + (unit_x - base_x) * (i * 2 * dash_length) / total_length
                    start_y = base_y + (unit_y - base_y) * (i * 2 * dash_length) / total_length
                    end_x = base_x + (unit_x - base_x) * (i * 2 * dash_length + dash_length) / total_length
                    end_y = base_y + (unit_y - base_y) * (i * 2 * dash_length + dash_length) / total_length
                    pygame.draw.line(screen, (0, 200, 0), (start_x, start_y), (end_x, end_y), 2)

    def draw_unit_paths(self):
        for unit in self.units:
            if unit.selected and unit.path:
                full_path = [unit.position]
                for node in unit.path:
                    full_path.append((self.graph.nodes[node]["y"], self.graph.nodes[node]["x"]))
                for i in range(len(full_path) - 1):
                    start_x, start_y = self.world_to_screen(full_path[i])
                    end_x, end_y = self.world_to_screen(full_path[i + 1])
                    dash_length = 5
                    dashes = [(start_x + j * (end_x - start_x) / dash_length,
                              start_y + j * (end_y - start_y) / dash_length,
                              start_x + (j + 0.5) * (end_x - start_x) / dash_length,
                              start_y + (j + 0.5) * (end_y - start_y) / dash_length)
                              for j in range(dash_length)]
                    for dash in dashes:
                        pygame.draw.line(screen, (255, 165, 0), (dash[0], dash[1]), (dash[2], dash[3]), 2)

    def draw_units(self):
        for unit in self.units:
            x, y = self.world_to_screen(unit.position)
            image = unit_images["infantry_brigade_moving"][int(time.time() * 5) % 4] if unit.is_moving() else unit_images["infantry_brigade"]
            image_rect = image.get_rect(center=(int(x), int(y)))
            screen.blit(image, image_rect)
            if unit.selected:
                alpha = 50 + int(50 * math.sin(time.time() * 5))
                selection_surface = pygame.Surface((image_rect.width + 10, image_rect.height + 10), pygame.SRCALPHA)
                selection_surface.fill((0, 255, 0, alpha))
                screen.blit(selection_surface, (image_rect.x - 5, image_rect.y - 5))
                pygame.draw.rect(screen, (0, 255, 0), image_rect.inflate(10, 10), 2)

    def draw_base(self):
        base_x, base_y = self.world_to_screen(self.base_position)
        pygame.draw.circle(screen, (0, 0, 255), (int(base_x), int(base_y)), 15)
        pygame.draw.circle(screen, (255, 255, 255), (int(base_x), int(base_y)), 10)
        screen.blit(font.render("Суми", True, (255, 255, 255)), (int(base_x) - 20, int(base_y) - 30))

    def draw_labels(self):
        """Відображаємо назви вулиць і міст"""
        for place in self.place_labels:
            x, y = self.world_to_screen(place["position"])
            if 0 <= x <= WIDTH and 0 <= y <= HEIGHT:
                label = label_font.render(place["name"], True, (255, 255, 255))
                label_rect = label.get_rect(center=(x, y - 20))
                pygame.draw.rect(screen, (0, 0, 0, 200), label_rect.inflate(4, 4))
                screen.blit(label, label_rect)

        if self.zoom >= 14:
            for street in self.street_labels:
                x, y = self.world_to_screen(street["position"])
                if 0 <= x <= WIDTH and 0 <= y <= HEIGHT:
                    label = label_font.render(street["name"], True, (200, 200, 200))
                    label_rect = label.get_rect(center=(x, y))
                    pygame.draw.rect(screen, (0, 0, 0, 150), label_rect.inflate(4, 4))
                    screen.blit(label, label_rect)

    def draw_ui(self):
        top_panel = pygame.Surface((WIDTH, TOP_PANEL_HEIGHT))
        top_panel.fill(DARK_GRAY)
        screen.blit(top_panel, (0, 0))
        
        resource_icons = [
            {"name": "manpower", "icon": "👥", "value": f"{self.resources['manpower']}"},
            {"name": "supplies", "icon": "📦", "value": f"{self.resources['supplies']}%"},
            {"name": "fuel", "icon": "⛽", "value": f"{self.resources['fuel']}%"},
            {"name": "equipment", "icon": "🔫", "value": f"{self.resources['equipment']}M"},
            {"name": "divisions", "icon": "⚔️", "value": f"{self.resources['divisions']}"},
            {"name": "efficiency", "icon": "⚙️", "value": f"{self.resources['efficiency']}"},
            {"name": "ships", "icon": "🚢", "value": f"{self.resources['ships']}"}
        ]
        
        x_offset = 10
        for resource in resource_icons:
            icon_text = small_font.render(resource["icon"], True, (255, 255, 255))
            value_text = small_font.render(resource["value"], True, (255, 255, 255))
            screen.blit(icon_text, (x_offset, 5))
            screen.blit(value_text, (x_offset + 20, 5))
            x_offset += 80
        
        date_text = small_font.render("1:00, 24 лют. 2022", True, (255, 255, 255))
        screen.blit(date_text, (WIDTH - 150, 5))
        
        roads_button = pygame.Rect(WIDTH - 150, TOP_PANEL_HEIGHT + 5, 140, 20)
        pygame.draw.rect(screen, LIGHT_GRAY, roads_button)
        screen.blit(small_font.render(f"{'Всі дороги: Так' if self.draw_all_roads else 'Всі дороги: Ні'}", True, (255, 255, 255)), (WIDTH - 145, TOP_PANEL_HEIGHT + 5))
        
        return roads_button

    def draw_sidebar(self):
        if not self.show_sidebar:
            return
        sidebar_surface = pygame.Surface((SIDEBAR_WIDTH, HEIGHT - TOP_PANEL_HEIGHT))
        sidebar_surface.fill(DARK_GRAY)
        screen.blit(sidebar_surface, (0, TOP_PANEL_HEIGHT))
        
        screen.blit(font.render("Підрозділи", True, (255, 255, 255)), (10, TOP_PANEL_HEIGHT + 10))
        
        select_all_button = pygame.Rect(SIDEBAR_WIDTH - 100, TOP_PANEL_HEIGHT + 10, 90, 25)
        pygame.draw.rect(screen, LIGHT_GRAY, select_all_button)
        screen.blit(small_font.render("Вибрати всі", True, (255, 255, 255)), (SIDEBAR_WIDTH - 95, TOP_PANEL_HEIGHT + 15))
        
        selected_count = sum(1 for unit in self.units if unit.selected)
        screen.blit(font.render(f"{selected_count} вибрано", True, (255, 255, 255)), (10, TOP_PANEL_HEIGHT + 40))
        
        icon_height = 30
        visible_height = HEIGHT - TOP_PANEL_HEIGHT
        total_height = len(self.units) * icon_height
        if total_height > visible_height - 70:
            self.sidebar_scroll = max(0, min(self.sidebar_scroll, total_height - (visible_height - 70)))
        
        for i, unit in enumerate(self.units):
            icon_y = TOP_PANEL_HEIGHT + 70 + i * icon_height - self.sidebar_scroll
            if icon_y + icon_height < TOP_PANEL_HEIGHT + 70 or icon_y > HEIGHT:
                continue
            icon_rect = pygame.Rect(5, icon_y, SIDEBAR_WIDTH - 10, icon_height - 2)
            pygame.draw.rect(screen, UI_BLUE if unit.selected else LIGHT_GRAY, icon_rect)
            icon_image = unit_images["infantry_brigade"]
            screen.blit(icon_image, icon_image.get_rect(center=(icon_rect.x + 15, icon_rect.y + icon_height//2)))
            screen.blit(small_font.render(unit.name, True, (255, 255, 255)), (icon_rect.x + 30, icon_rect.y + 5))
            org_bar_rect = pygame.Rect(icon_rect.x + 150, icon_rect.y + 10, 80, 10)
            pygame.draw.rect(screen, (100, 100, 100), org_bar_rect)
            org_fill_rect = pygame.Rect(org_bar_rect.x, org_bar_rect.y, org_bar_rect.width * unit.organization / 100, org_bar_rect.height)
            pygame.draw.rect(screen, (0, 255, 0), org_fill_rect)
        
        return select_all_button

    def draw_selection_box(self):
        if self.selection_box_active and self.selection_start and self.selection_current:
            drag_distance = ((self.selection_start[0] - self.selection_current[0])**2 + 
                            (self.selection_start[1] - self.selection_current[1])**2)**0.5
            if drag_distance < 5:
                return
            x1, y1 = min(self.selection_start[0], self.selection_current[0]), min(self.selection_start[1], self.selection_current[1])
            x2, y2 = max(self.selection_start[0], self.selection_current[0]), max(self.selection_start[1], self.selection_current[1])
            selection_surface = pygame.Surface((x2 - x1, y2 - y1), pygame.SRCALPHA)
            selection_surface.fill((0, 255, 0, 50))
            screen.blit(selection_surface, (x1, y1))
            pygame.draw.rect(screen, (0, 255, 0), pygame.Rect(x1, y1, x2 - x1, y2 - y1), 2)

    def draw_minimap(self):
        minimap_size = 150
        minimap_surface = pygame.Surface((minimap_size, minimap_size))
        minimap_surface.fill(DARK_GRAY)
        minimap_surface.set_alpha(200)
        minimap_zoom = self.zoom - 4
        if minimap_zoom < 1:
            minimap_zoom = 1
        
        top_left = self.screen_to_world((0, 0))
        bottom_right = self.screen_to_world((WIDTH, HEIGHT))
        x_tile_min, y_tile_min = self.latlon_to_tile(top_left[0], top_left[1], minimap_zoom)
        x_tile_max, y_tile_max = self.latlon_to_tile(bottom_right[0], bottom_right[1], minimap_zoom)
        
        for x_tile in range(x_tile_min - 2, x_tile_max + 3):
            for y_tile in range(y_tile_min - 2, y_tile_max + 3):
                tile = self.load_tile(x_tile, y_tile, minimap_zoom)
                tile_lat, tile_lon = self.tile_to_latlon(x_tile, y_tile, minimap_zoom)
                center_x_tile, center_y_tile = self.latlon_to_tile(self.center_lat, self.center_lon, minimap_zoom)
                center_tile_lat, center_tile_lon = self.tile_to_latlon(center_x_tile, center_y_tile, minimap_zoom)
                
                n = 2 ** minimap_zoom
                scale = n * TILE_SIZE / 360.0
                mini_x = (tile_lon - center_tile_lon) * scale + minimap_size / 2
                mini_y = (center_tile_lat - tile_lat) * scale + minimap_size / 2
                minimap_surface.blit(tile, (int(mini_x), int(mini_y)))
        
        pygame.draw.circle(minimap_surface, (0, 0, 255), (minimap_size // 2, minimap_size // 2), 3)
        for unit in self.units:
            unit_x_tile, unit_y_tile = self.latlon_to_tile(unit.position[0], unit.position[1], minimap_zoom)
            unit_tile_lat, unit_tile_lon = self.tile_to_latlon(unit_x_tile, unit_y_tile, minimap_zoom)
            mini_x = (unit_tile_lon - center_tile_lon) * scale + minimap_size / 2
            mini_y = (center_tile_lat - unit.position[0]) * scale + minimap_size / 2
            if 0 <= mini_x <= minimap_size and 0 <= mini_y <= minimap_size:
                color = (0, 255, 0) if unit.selected else (255, 0, 0)
                pygame.draw.circle(minimap_surface, color, (int(mini_x), int(mini_y)), 2)
        
        view_width = WIDTH / (2 ** self.zoom) * (2 ** minimap_zoom) * TILE_SIZE / 360.0
        view_height = HEIGHT / (2 ** self.zoom) * (2 ** minimap_zoom) * TILE_SIZE / 360.0
        pygame.draw.rect(minimap_surface, (255, 0, 0), 
                        (minimap_size / 2 - view_width / 2, minimap_size / 2 - view_height / 2, view_width, view_height), 1)
        screen.blit(minimap_surface, (WIDTH - minimap_size - 10, HEIGHT - minimap_size - 10))
        screen.blit(small_font.render("Міні-карта", True, (255, 255, 255)), (WIDTH - minimap_size - 10, HEIGHT - minimap_size - 30))

    def draw(self):
        screen.fill((255, 255, 255))  # Білий фон на випадок, якщо тайли не завантажилися
        self.draw_map()
        self.draw_roads()
        self.draw_labels()
        self.draw_supply_lines()
        self.draw_unit_paths()
        self.draw_base()
        self.draw_units()
        self.draw_selection_box()
        self.draw_minimap()
        roads_button = self.draw_ui()
        select_all_button = self.draw_sidebar()
        mouse_pos = pygame.mouse.get_pos()
        mouse_clicked = pygame.mouse.get_pressed()[0]
        self.handle_zoom_buttons(mouse_pos, mouse_clicked)
        return roads_button, select_all_button

    def run(self):
        clock = pygame.time.Clock()
        running = True
        roads_button = None
        select_all_button = None
        while running:
            dt = clock.tick(60)
            for event in pygame.event.get():
                if event.type == pygame.QUIT:
                    running = False
                self.handle_mouse_events(event)
                if event.type == pygame.MOUSEBUTTONDOWN:
                    pos = pygame.mouse.get_pos()
                    if roads_button and roads_button.collidepoint(pos):
                        self.draw_all_roads = not self.draw_all_roads
                        logger.info(f"Toggle all roads: {self.draw_all_roads}")
                    if select_all_button and select_all_button.collidepoint(pos):
                        if all(unit.selected for unit in self.units):
                            for unit in self.units:
                                unit.selected = False
                        else:
                            for unit in self.units:
                                unit.selected = True
                        logger.info("Toggle select all units")
                self.handle_zoom(event)
            keys = pygame.key.get_pressed()
            if keys[pygame.K_LCTRL] and keys[pygame.K_a]:
                for unit in self.units:
                    unit.selected = True
                logger.info("Selected all units with Ctrl+A")
            self.handle_camera_control()
            for unit in self.units:
                unit.move(self.graph, dt)
            roads_button, select_all_button = self.draw()
            pygame.display.flip()
        pygame.quit()

if __name__ == "__main__":
    try:
        logger.info("Combrig starting...")
        game = Game()
        game.run()
    except Exception as e:
        logger.error(f"Combrig crashed: {e}", exc_info=True)
        print(f"Error: {e}")