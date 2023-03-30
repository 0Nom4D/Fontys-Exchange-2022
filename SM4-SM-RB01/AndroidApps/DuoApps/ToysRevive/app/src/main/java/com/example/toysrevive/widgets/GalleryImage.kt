package com.example.toysrevive.widgets

import android.net.Uri

import androidx.activity.compose.rememberLauncherForActivityResult
import androidx.activity.result.contract.ActivityResultContracts

import androidx.compose.foundation.Image
import androidx.compose.foundation.background
import androidx.compose.foundation.layout.*
import androidx.compose.foundation.shape.CircleShape
import androidx.compose.foundation.shape.RoundedCornerShape

import androidx.compose.material.Card
import androidx.compose.material.Icon
import androidx.compose.material.IconButton
import androidx.compose.material.MaterialTheme
import androidx.compose.material.icons.Icons
import androidx.compose.material.icons.filled.Close

import androidx.compose.runtime.*

import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.draw.clip
import androidx.compose.ui.graphics.Color
import androidx.compose.ui.graphics.vector.ImageVector
import androidx.compose.ui.platform.LocalContext
import androidx.compose.ui.res.vectorResource
import androidx.compose.ui.unit.dp

import coil.compose.rememberAsyncImagePainter
import coil.request.ImageRequest

import com.example.toysrevive.R

@Composable
fun GalleryImage(
    image: Uri?,
    onUpdate: (Uri?) -> Unit,
    modifier: Modifier = Modifier
) {
    var imageUri by remember { mutableStateOf(image) }
    val launcher = rememberLauncherForActivityResult(contract = ActivityResultContracts.GetContent()) { uri ->
        imageUri = uri
        onUpdate(uri)
    }

    Card(
        backgroundColor = if (imageUri == null) MaterialTheme.colors.surface else Color.Transparent,
        shape = RoundedCornerShape(10.dp),
        modifier = modifier
            .fillMaxHeight(.15f)
            .aspectRatio(1f)
            .padding(7.dp)
    ) {
        Box(contentAlignment = Alignment.Center, modifier = Modifier.fillMaxSize().background(
            if (imageUri == null) MaterialTheme.colors.surface else Color.Transparent
        )) {
            if (imageUri == null) {
                IconButton(
                    onClick = { launcher.launch("image/*") },
                    modifier = Modifier.fillMaxSize()
                ) {
                    Icon(
                        ImageVector.vectorResource(id = R.drawable.outline_photo_camera_24),
                        contentDescription = "Add picture for toy ad"
                    )
                }
            } else {
                Card(contentColor = Color.Yellow, backgroundColor = MaterialTheme.colors.background, modifier = Modifier.fillMaxSize()) {
                    Image(
                        painter = rememberAsyncImagePainter(
                            ImageRequest
                                .Builder(LocalContext.current)
                                .data(data = imageUri)
                                .build()
                        ),
                        contentDescription = "Toy picture with value $imageUri",
                    )
                }
                IconButton(
                    onClick = {
                        imageUri = null
                        onUpdate(null)
                    },
                    modifier = Modifier
                        .clip(CircleShape)
                        .background(Color.White)
                        .size(15.dp)
                        .align(Alignment.TopEnd)
                ) {
                    Icon(
                        Icons.Default.Close,
                        tint = Color.Gray,
                        contentDescription = "Delete the picture from the ad",
                        modifier = Modifier.size(20.dp).align(Alignment.TopEnd)
                    )
                }
            }
        }
    }
}