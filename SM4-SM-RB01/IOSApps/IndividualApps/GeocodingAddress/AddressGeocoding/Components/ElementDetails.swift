//
//  ElementDetails.swift
//  AddressGeocoding
//
//  Created by Nom4D on 28/03/2023.
//

import SwiftUI

struct ElementDetails: View {
    @EnvironmentObject private var geocoderHandler: GeocoderHandler

    var locationName: String
    var locationAdditionalName: String

    var body: some View {
        VStack {
            HStack(alignment: .top, spacing: 0) {
                Text(locationName)
                    .font(.system(size: 35, weight: .bold, design: .default))
                    .frame(maxWidth: .infinity, alignment: .leading)
                    .bold()
                    .padding(.leading, 8)
                Button(action: {
                    geocoderHandler.currentLocation.coordinates = nil
                    geocoderHandler.isDetailed = false
                    geocoderHandler.request = ""
                }) {
                    Image(systemName: "xmark.circle.fill")
                        .aspectRatio(contentMode: .fill)
                        .frame(maxWidth: 50, maxHeight: 50)
                }
            }
            Text("\(locationName), \(locationAdditionalName)")
                .font(.system(size: 10, weight: .regular, design: .default))
                .frame(maxWidth: .infinity, alignment: .leading)
                .bold()
                .padding(.leading, 8)
        }
    }
}
