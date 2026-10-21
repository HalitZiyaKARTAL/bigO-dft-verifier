def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


schedule = [
    43, 43, 39, 39, 40, 40, 37, 36, 34, 32,
    30, 28, 26, 24, 23, 22, 20, 19, 18, 15,
]
depth, block_size, initial_blocks, copies = 20, 22, 2**18, 99
zero_profiles = [block_size - index for index in range(1, depth + 2)]
one_profiles = [
    block_size * initial_blocks - depth - 1 + index
    for index in range(1, depth + 2)
]
joint_zero = joint_one = 0
block_count = copies * initial_blocks

for exponent in schedule:
    outdegree, threshold = 2**exponent, exponent + 6
    vertices = 2 * outdegree + 1
    require(
        vertices**threshold * 4**threshold
        < 4 ** (threshold * (threshold - 1) // 2),
        "labels",
    )
    parent_count = len(zero_profiles) - 1
    next_zero = [
        (threshold - 1) * zero_profiles[-1]
        + max(one_profiles[parent_count - index] + joint_one, 3 * joint_one)
        for index in range(1, parent_count + 1)
    ]
    next_one = [
        outdegree * zero_profiles[parent_count - index] + 4 * one_profiles[-1]
        for index in range(1, parent_count + 1)
    ]
    next_joint_zero = (threshold - 1) * zero_profiles[-1] + 3 * joint_one
    next_joint_one = outdegree * joint_zero + 4 * one_profiles[-1]
    zero_profiles, one_profiles = next_zero, next_one
    joint_zero, joint_one = next_joint_zero, next_joint_one
    block_count *= vertices

sensitivity_bound = int(
    "471911296125319941631870071456581119443681693706"
    "9042426143480674986488653925266778135905544699904"
)
expected_zero = int(
    "474556482057349399535164626349137929538981513603883148"
    "10566933912140678997965564602948079321088"
)
expected_blocks = int(
    "289081676577626660116933013288798039163776467005022844210388001576"
    "113891462263420603625898576050351912381269780409737335567160292764"
    "09483244766742429309394526056339187169947071319635328962185134080"
)
require(
    zero_profiles == [expected_zero] and one_profiles == [sensitivity_bound],
    "final profiles",
)
require(block_count == expected_blocks, "block count")
require(copies * zero_profiles[0] <= sensitivity_bound, "OR balancing")
require(block_count**187 > sensitivity_bound**380, "strict exponent")
require(380 * 1000000 > 2032083 * 187, "exact root threshold")
require((100 * 2**646) ** 187 < (9 * 2**318) ** 380, "frozen comparison")
print("PASS: exact seed and strict exponent inequalities")
