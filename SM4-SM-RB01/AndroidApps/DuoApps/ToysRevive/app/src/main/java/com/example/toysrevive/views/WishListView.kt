package com.example.toysrevive.views

import android.Manifest
import android.app.Activity

import android.content.Intent
import android.content.pm.PackageManager

import android.net.Uri

import androidx.compose.foundation.Image
import androidx.compose.foundation.border
import androidx.compose.foundation.layout.*
import androidx.compose.foundation.lazy.grid.GridCells
import androidx.compose.foundation.lazy.grid.LazyVerticalGrid
import androidx.compose.foundation.shape.CircleShape

import androidx.compose.material.*
import androidx.compose.material.icons.Icons
import androidx.compose.material.icons.filled.Close

import androidx.compose.runtime.*

import kotlinx.coroutines.CoroutineScope

import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.draw.clip
import androidx.compose.ui.graphics.Color
import androidx.compose.ui.layout.ContentScale
import androidx.compose.ui.platform.LocalContext
import androidx.compose.ui.res.painterResource
import androidx.compose.ui.text.font.FontWeight
import androidx.compose.ui.text.style.TextAlign
import androidx.compose.ui.unit.dp
import androidx.compose.ui.unit.sp

import androidx.core.app.ActivityCompat
import androidx.core.content.ContextCompat

import androidx.navigation.NavHostController

import coil.compose.rememberAsyncImagePainter
import coil.request.ImageRequest

import com.example.toysrevive.R
import com.example.toysrevive.Screen
import com.example.toysrevive.ui.theme.getPoppins
import com.example.toysrevive.utils.GlobalSettings

import kotlinx.coroutines.launch

@Composable
fun WishListScreen(scaffoldState: ScaffoldState, navController: NavHostController, modifier: Modifier = Modifier) {
    val coroutineScope: CoroutineScope = rememberCoroutineScope()

    val context = LocalContext.current

    if (GlobalSettings.likedToys.isNotEmpty()) {
        LazyVerticalGrid(verticalArrangement = Arrangement.Center, columns = GridCells.Adaptive(175.dp), modifier = modifier) {
            items(GlobalSettings.likedToys.size) { idx ->
                Card(
                    elevation = 5.dp,
                    backgroundColor = MaterialTheme.colors.surface,
                    modifier = Modifier
                        .fillMaxWidth()
                        .padding(10.dp)
                ) {
                    Column(
                        verticalArrangement = Arrangement.SpaceEvenly,
                        horizontalAlignment = Alignment.CenterHorizontally,
                        modifier = Modifier.fillMaxWidth(.9f)
                    ) {
                        IconButton(
                            onClick = {
                                val lastDeletedToy = GlobalSettings.likedToys[idx]
                                GlobalSettings.dislikeToy(lastDeletedToy)
                                coroutineScope.launch {
                                    when (scaffoldState.snackbarHostState.showSnackbar("The toy you liked has been removed.", "Undo")) {
                                        SnackbarResult.ActionPerformed -> GlobalSettings.likeToyAndPlaceAt(lastDeletedToy, idx)
                                        else -> {}
                                    }
                                }
                            },
                            modifier = Modifier.align(Alignment.End)
                        ) {
                            Icon(
                                Icons.Default.Close,
                                tint = Color.LightGray,
                                contentDescription = "Delete the toy from wish list",
                            )
                        }
                        Image(
                            painter = when (GlobalSettings.likedToys[idx].isCreated) {
                                false -> painterResource(id = GlobalSettings.likedToys[idx].pictures[0] as Int)
                                true -> rememberAsyncImagePainter(
                                    ImageRequest
                                        .Builder(LocalContext.current)
                                        .data(data = GlobalSettings.likedToys[idx].pictures[0] as Uri)
                                        .build()
                                )
                            },
                            contentDescription = "Picture of toy $idx",
                            contentScale = ContentScale.Crop,
                            modifier = Modifier
                                .padding(top = 1.dp, bottom = 15.dp, start = 15.dp, end = 15.dp)
                                .size(120.dp)
                                .clip(CircleShape)
                                .border(1.dp, Color.Black, CircleShape)
                        )
                        Text(
                            GlobalSettings.likedToys[idx].name,
                            fontSize = 18.sp,
                            fontFamily = getPoppins(),
                            color = Color.Black,
                            textAlign = TextAlign.Center,
                            modifier = Modifier.padding(vertical = 10.dp)
                        )
                        Button(
                            onClick = {
                                if (ContextCompat.checkSelfPermission(context, Manifest.permission.CALL_PHONE) == PackageManager.PERMISSION_GRANTED) {
                                    val phoneNumber = GlobalSettings.likedToys[idx].givingUser.phoneNumber
                                    val intent = Intent(Intent.ACTION_CALL, Uri.parse("tel:$phoneNumber"))
                                    context.startActivity(intent)
                                } else {
                                    ActivityCompat.requestPermissions(
                                        context as Activity,
                                        arrayOf(Manifest.permission.CALL_PHONE),
                                        0
                                    )
                                }
                            },
                            elevation = ButtonDefaults.elevation(
                                defaultElevation = 10.dp,
                                pressedElevation = 15.dp,
                                disabledElevation = 0.dp
                            ),
                            modifier = Modifier.padding(10.dp)
                        ) {
                            Text(
                                text = "Contact the owner",
                                fontFamily = getPoppins(),
                                fontWeight = FontWeight.Bold,
                                fontSize = 10.sp,
                                color = Color.White
                            )
                        }
                    }
                }
            }
        }
    } else {
        Column(horizontalAlignment = Alignment.CenterHorizontally, verticalArrangement = Arrangement.Center, modifier = modifier.fillMaxSize()) {
            Icon(
                painterResource(id = R.drawable.baseline_no_likes_24),
                contentDescription = null,
                modifier = Modifier.fillMaxSize(.6f)
            )
            Text(
                "You didn't liked toys for the moment. Check available toys!",
                textAlign = TextAlign.Center,
                fontFamily = getPoppins(),
                fontWeight = FontWeight.Medium,
                fontSize = 12.sp,
            )
            Spacer(modifier = Modifier.height(5.dp))
            Button(
                onClick = {
                    navController.navigate(Screen.SwipeScreen.route) {
                        navController.graph.startDestinationRoute?.let {route ->
                            popUpTo(route) {
                                saveState = true
                            }
                        }
                        launchSingleTop = true
                        restoreState = true
                    }
                }
            ) { Text("Check the available toys", fontFamily = getPoppins()) }
        }
    }
}