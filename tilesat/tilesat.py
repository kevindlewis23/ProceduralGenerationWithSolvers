from random import Random

import yaml
from pysat.solvers import Cadical300, Glucose4, Minicard, Gluecard4, Glucose42
from pysat.card import *
from pysat.formula import *

# Enumeration of connection directions
TOP = "top"
BOTTOM = "bottom"
LEFT = "left"
RIGHT = "right"



class Tile:
    def __init__(self, filename, rotation, connections):
        self.filename = filename
        self.rotation = rotation
        self.connections = connections
        self.has_left_connection = LEFT in self.connections
        self.has_right_connection = RIGHT in self.connections
        self.has_top_connection = TOP in self.connections
        self.has_bottom_connection = BOTTOM in self.connections


    def get_pil_image(self):
        from PIL import Image
        image = Image.open(f"tileset/{self.filename}")
        rotation = int(self.rotation)
        if rotation == 90:
            image = image.transpose(Image.Transpose.ROTATE_90)
        elif rotation == 180:
            image = image.transpose(Image.Transpose.ROTATE_180)
        elif rotation == 270:
            image = image.transpose(Image.Transpose.ROTATE_270)
        # Replace transparent background with white
        background = Image.new("RGB", image.size, (255, 255, 255))
        background.paste(image, mask=image.split()[3])
        image = background
        return image

def get_all_tiles() -> list[Tile]:

    with open("tileset/tiles.yaml", "r") as file:
        tiles_data = yaml.safe_load(file)

    tiles = [Tile(tile['filename'], tile['rotation'], tile['connections']) for tile in tiles_data]
    return tiles

# Turn a list of tiles into an image
def draw_map(tiles: list[Tile], tile_size: int, tile_indices: list[list[int]]):
    from PIL import Image
    map_width = len(tile_indices[0]) * tile_size
    map_height = len(tile_indices) * tile_size
    map_image = Image.new("RGB", (map_width, map_height))

    for y, row in enumerate(tile_indices):
        for x, tile_index in enumerate(row):
            tile = tiles[tile_index]
            tile_image = tile.get_pil_image()
            # tile_image = tile_image.resize((tile_size, tile_size))
            map_image.paste(tile_image, (x * tile_size, y * tile_size))

    map_image.show()
    input("Press Enter to save the image as output.png...")
    map_image.save("output.png")


def solve(width: int, height: int, tiles: list[Tile]):
    """
    We will construct the SAT clauses where the first width * height * num_tiles variables correspond to whether a tile at a location can be of a certain type
    The next (width+1) * height variables correspond to whether a connection exists between two tiles horizontally (outer 2 columns are for the left and right edges)
    The next width * (height1) variables correspond to whether a connection exists between two tiles vertically
    Then we solve
    """
    num_tiles = len(tiles)
    solver = Gluecard4()

    # What type of encoding to tuse for cardinality constraints
    card_enc = EncType.native
    vpool = IDPool()
    # Construct a mapping between variables and their corresponding indices
    def get_variable_index(x, y, tile_index):
        return (y * width + x) * num_tiles + tile_index + 1  # +1 because SAT solvers expect variables to be 1-indexed
    def get_variable_coordinates(variable_index):
        var_index = variable_index - 1  # Convert back to 0-indexed
        tile_index = var_index % num_tiles
        x = (var_index // num_tiles) % width
        y = var_index // (num_tiles * width)
        return x, y, tile_index

    num_type_variables = width * height * num_tiles
    num_horizontal_connection_variables = (width + 1) * height
    num_vertical_connection_variables = width * (height + 1)
    # Create the connection variables in the vpool
    vpool.top = num_type_variables + num_horizontal_connection_variables + num_vertical_connection_variables + 1

    # Note that connection variable (x,y, true) is the horizontal connection between (x-1,y) and (x,y)
    # Note that connection variable (x,y, false) is the vertical connection between (x,y-1) and (x,y)
    # The boundaries are represented with -1 and width or height
    def get_connection_variable_index(x, y, is_horizontal):
        if is_horizontal:
            assert 0 <= x <= width, "x must be in the range [0, width] for horizontal connections"
            assert 0 <= y < height, "y must be in the range [0, height-1] for horizontal connections"
            return y * (width+1) + x + num_type_variables + 1
        else:
            assert 0 <= x < width, "x must be in the range [0, width-1] for vertical connections"
            assert 0 <= y <= height, "y must be in the range [0, height] for vertical connections"
            return y * width + x + num_type_variables + num_horizontal_connection_variables + 1

    # For each location, construct a clause saying exactly at least one tile must be placed there
    # If we get multiple, then we will be able to choose any
    for y in range(height):
        for x in range(width):
            solver.add_clause([get_variable_index(x, y, tile_index) for tile_index in range(num_tiles)])
    # Define the horizontal connection clauses
    for y in range(height):
        for x in range(width + 1):
            connection_variable_index = get_connection_variable_index(x, y, True)
            for tile_index in range(num_tiles):
                tile = tiles[tile_index]
                # If there is a tile to the left
                if x > 0:
                    left_tile_index = get_variable_index(x - 1, y, tile_index)
                    # If the left tile has a right connection, then the connection variable must be true
                    # If the left tile does not have a right connection, then the connection variable must be false
                    if tile.has_right_connection:
                        solver.add_clause([-left_tile_index, connection_variable_index])
                    else:
                        solver.add_clause([-left_tile_index, -connection_variable_index])

                # Same on the right side
                if x < width:
                    right_tile_index = get_variable_index(x, y, tile_index)
                    if tile.has_left_connection:
                        solver.add_clause([-right_tile_index, connection_variable_index])
                    else:
                        solver.add_clause([-right_tile_index, -connection_variable_index])
    # Define the vertical connection clauses
    for y in range(height + 1):
        for x in range(width):
            connection_variable_index = get_connection_variable_index(x, y, False)
            for tile_index in range(num_tiles):
                tile = tiles[tile_index]
                if y > 0:
                    top_tile_index = get_variable_index(x, y - 1, tile_index)
                    # If the top tile has a bottom connection, then the connection variable must be true
                    # If the top tile does not have a bottom connection, then the connection variable must be false
                    if tile.has_bottom_connection:
                        solver.add_clause([-top_tile_index, connection_variable_index])
                    else:
                        solver.add_clause([-top_tile_index, -connection_variable_index])

                # Same on the bottom side
                if y < height:
                    bottom_tile_index = get_variable_index(x, y, tile_index)
                    if tile.has_top_connection:
                        solver.add_clause([-bottom_tile_index, connection_variable_index])
                    else:
                        solver.add_clause([-bottom_tile_index, -connection_variable_index])


    # BOUNDS_ON_NUM_OUTSIDE_CONNECTIONS = [2,2]
    

    # # Add a cardinality constraint on the number of true outside connections
    # outside_connections = []
    # for y in range(height):
    #     outside_connections.append(get_connection_variable_index(0, y, True))  # Left edge
    #     outside_connections.append(get_connection_variable_index(width, y, True))  # Right edge
    # for x in range(width):
    #     outside_connections.append(get_connection_variable_index(x, 0, False))  # Top edge
    #     outside_connections.append(get_connection_variable_index(x, height, False))  # Bottom edge

    # # Add the cardinality constraint
    # atmost_constraint= CardEnc.atmost(lits=outside_connections, bound=BOUNDS_ON_NUM_OUTSIDE_CONNECTIONS[1], vpool=vpool, encoding=card_enc)
    # atleast_constraint = CardEnc.atleast(lits=outside_connections, bound=BOUNDS_ON_NUM_OUTSIDE_CONNECTIONS[0], vpool=vpool, encoding=card_enc)
    # solver.append_formula(atmost_constraint)
    # solver.append_formula(atleast_constraint)
    # Only the top left and bottom right corners can have outside connections
    for y in range(1, height-1):
        solver.add_clause([-get_connection_variable_index(0, y, True)])  # Left edge
        solver.add_clause([-get_connection_variable_index(width, y, True)])  # Right edge
    solver.add_clause([get_connection_variable_index(0, 0, True)])  # Top left corner
    solver.add_clause([-get_connection_variable_index(width, 0, True)])  # Top right corner
    solver.add_clause([-get_connection_variable_index(0, height-1, True)])
    solver.add_clause([get_connection_variable_index(width, height-1, True)])  # Bottom right corner


    # None of the top or bottom edges can have outside connections
    for x in range(width):
        solver.add_clause([-get_connection_variable_index(x, 0, False)])  # Top edge
        solver.add_clause([-get_connection_variable_index(x, height, False)])  # Bottom edge


    # Add max number of each type of tile constraint
    MAX_OF_EACH_TYPE = 900
    # Add a cardinality constraint on the number of each type of tile
    for tile_index in range(num_tiles):
        tile_variables = [get_variable_index(x, y, tile_index) for y in range(height) for x in range(width)]
        atmost_constraint = CardEnc.atmost(lits=tile_variables, bound=MAX_OF_EACH_TYPE, vpool=vpool, encoding=card_enc)
        solver.append_formula(atmost_constraint)


    # Add a reachability constrant, everything should be reachable from everything else.
    # To do this, we create a bunch of new variables for each tile to say whether or not it is reachable from (0,0) in k steps
    NUM_REACHABILITY_STEPS = 4 *(width + height)
    top_before_reachability = vpool.top
    def get_reachable_variable_index(x, y, k):
        return (y * width + x) * NUM_REACHABILITY_STEPS + k + top_before_reachability + 1
    vpool.top += width * height * NUM_REACHABILITY_STEPS
    
    # (0,0) is reachable from (0,0) in 0 steps, and no other tile is reachable in 0 steps
    # Every tile must be reachable in NUM_REACHABILITY_STEPS steps
    for y in range(height):
        for x in range(width):
            if (x, y) == (0, 0):
                solver.add_clause([get_reachable_variable_index(x, y, 0)])
            else:
                solver.add_clause([-get_reachable_variable_index(x, y, 0)])
            solver.add_clause([get_reachable_variable_index(x, y, NUM_REACHABILITY_STEPS - 1)])


    # For larger k, a tile is reachable in k steps if it or any of its neighbors is reachable in k-1 steps
    for k in range(1, NUM_REACHABILITY_STEPS):
        for y in range(height):
            for x in range(width):
                if (x, y) != (0, 0):
                    # Encode (reachable at step k) => (some neighbor or self reachable at k-1)
                    neighbors = []
                    if x > 0:
                        neighbors.append((get_reachable_variable_index(x - 1, y, k-1), get_connection_variable_index(x, y, True)))
                    if x < width - 1:
                        neighbors.append((get_reachable_variable_index(x + 1, y, k-1), get_connection_variable_index(x + 1, y, True)))
                    if y > 0:
                        neighbors.append((get_reachable_variable_index(x, y - 1, k-1), get_connection_variable_index(x, y, False)))
                    if y < height - 1:
                        neighbors.append((get_reachable_variable_index(x, y + 1, k-1), get_connection_variable_index(x, y + 1, False)))

                    # Create a clause for the reachability constraint.
                    # It should look like current <=> ((neighbor1 and connection1) or (neighbor2 and connection2) or ...)
                    current = get_reachable_variable_index(x, y, k)
                    current_before = get_reachable_variable_index(x, y, k-1)
                    right_side_ands = [Atom(neighbor) & Atom(connection) for neighbor, connection in neighbors]
                    if right_side_ands:
                        # some neighbor or self reachable at k-1
                        right_side_or = Or(Atom(current_before), *right_side_ands)
                        # With the implies before it
                        full_formula = Implies(Atom(current), right_side_or)
                        full_formula.attach_vpool(vpool)
                        solver.append_formula(full_formula)

    # Make sure it's acyclic graph.
    # Asuming reachability, we can verify this from the number of internal connections (needs to be 1 fewer than the number of tiles)
    # internal_connections = [get_connection_variable_index(x + 1, y,  True) for y in range(height) for x in range(width - 1)] + \
    #                        [get_connection_variable_index(x, y + 1, False) for y in range(height - 1) for x in range(width)]
    # internal_connection_constraint = CardEnc.atmost(lits=internal_connections, bound=(width * height) - 1, vpool=vpool, encoding=card_enc)
    # solver.append_formula(internal_connection_constraint)
                


    # Add a seed
    # random = Random()
    # # Pick one random index and tile to seed the problem with
    # solver.add_clause([random.randint(1, num_type_variables)]) 
    # # solver.add_clause([-get_variable_index(2,2,0)])
    # Check if the problem is satisfiable
    if solver.solve():
        print("The problem is satisfiable.")
    else:
        print("The problem is not satisfiable.")
        return None
    model = solver.get_model()
    assert model is not None, "Model should not be None if the problem is satisfiable"

    true_variables = set(var for var in model if var > 0)

    # Return the tile indices placed in each location
    result = []
    for y in range(height):
        row = []
        for x in range(width):
            for tile_index in range(num_tiles):
                if get_variable_index(x, y, tile_index) in true_variables:
                    row.append(tile_index)
                    break
            else:
                print(f"Error No tile found for position ({x}, {y})")
                return None
        result.append(row)

    return result


tiles = get_all_tiles()
TILE_SIZE = 16
result = solve(20,20,tiles)
if result is not None:
    draw_map(tiles, TILE_SIZE, result)
