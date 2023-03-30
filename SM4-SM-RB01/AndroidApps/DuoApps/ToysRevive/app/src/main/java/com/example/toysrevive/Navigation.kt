package com.example.toysrevive

import androidx.compose.material.ExperimentalMaterialApi
import androidx.compose.material.ModalBottomSheetState
import androidx.compose.material.ScaffoldState
import androidx.compose.runtime.Composable
import androidx.compose.ui.Modifier

import androidx.navigation.NavHostController
import androidx.navigation.compose.NavHost
import androidx.navigation.compose.composable

import com.example.toysrevive.views.AdCreationView
import com.example.toysrevive.views.SwipingScreen
import com.example.toysrevive.views.WishListScreen

@OptIn(ExperimentalMaterialApi::class)
@Composable
fun Navigation(scaffoldState: ScaffoldState, navController: NavHostController, bottomSheetState: ModalBottomSheetState, modifier: Modifier = Modifier) {
    NavHost(navController = navController, startDestination = Screen.SwipeScreen.route) {
        composable(route = Screen.SwipeScreen.route) {
            SwipingScreen(bottomSheetState, modifier)
        }

        composable(route = Screen.WishListScreen.route) {
            WishListScreen(scaffoldState, navController, modifier)
        }

        composable(route = Screen.ToyAdCreation.route) {
            AdCreationView(scaffoldState, modifier)
        }
    }
}