package com.example.toysrevive

sealed class Screen(val screenName: String, val route: String, val displayName: String) {
    object SwipeScreen : Screen("Toy List", "main_screen", "")
    object ToyAdCreation : Screen("Create A List", "ad_creation", "Post A Toy")
    object WishListScreen : Screen("Saved Toys", "wish_list_screen", "Saved Toys")

}

fun getRouteDisplayName(route: String?) : String? {
    val screenRoutes = listOf(
        Screen.WishListScreen,
        Screen.SwipeScreen,
        Screen.ToyAdCreation
    )

    if (route == null) {
        return null;
    }

    screenRoutes.forEach { screen ->
        if (screen.route == route) {
            return screen.displayName
        }
    }
    return null;
}
