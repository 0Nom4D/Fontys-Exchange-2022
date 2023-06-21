package com.example.hapticfeedbacktechcase

import android.os.Build
import android.os.Bundle
import android.os.Vibrator

import androidx.activity.compose.setContent
import androidx.annotation.RequiresApi
import androidx.appcompat.app.AppCompatActivity

import androidx.compose.foundation.layout.*
import androidx.compose.material.*
import androidx.compose.runtime.*
import androidx.compose.ui.Modifier
import androidx.compose.ui.unit.dp

import androidx.navigation.compose.rememberNavController

import com.example.hapticfeedbacktechcase.composables.BottomNavBar

class MainActivity : AppCompatActivity() {
    @RequiresApi(Build.VERSION_CODES.R)
    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)
        setContent {
            val navController = rememberNavController()
            val scaffoldState = rememberScaffoldState()

            val vibrator = applicationContext.getSystemService(Vibrator::class.java)

            Scaffold(
                topBar = {
                    TopAppBar(
                        title = {
                            Text("Tech Case n°7: Haptics")
                        },
                        backgroundColor = MaterialTheme.colors.primary,
                        elevation = 10.dp
                    )
                },
                bottomBar = { BottomNavBar(navController = navController) },
                scaffoldState = scaffoldState,
                modifier = Modifier.fillMaxSize()
            ) {
                Navigation(
                    vibrator = vibrator,
                    scaffoldState = scaffoldState,
                    navController = navController,
                    modifier = Modifier.padding(it)
                )
            }
        }
    }
}
